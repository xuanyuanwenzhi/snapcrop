# SnapCrop - lightweight desktop image crop & edit tool
# 说明：本项目在 GPT 的协助下完成（部分功能思路与代码结构由 GPT 提供建议）。

import os
import math
import secrets  # 用于生成更可靠的随机数（这里用来做 4 位随机后缀）
import webbrowser
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser
from PIL import Image, ImageTk, ImageOps, ImageEnhance


class ScrollableFrame(ttk.Frame):
    """
    Notebook 的每个 Tab 用这个包一层：
    - 内容超高自动滚动
    - 鼠标滚轮在该区域内生效
    """
    def __init__(self, master, *, bg=None, **kwargs):
        super().__init__(master, **kwargs)

        self.canvas = tk.Canvas(self, highlightthickness=0, bd=0)
        self.vbar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vbar.set)

        self.inner = ttk.Frame(self)

        self._win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")

        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.vbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.inner.bind("<Configure>", self._on_inner_configure)
        self.canvas.bind("<Configure>", self._on_canvas_configure)

        # 鼠标滚轮：进入区域才滚
        self.canvas.bind("<Enter>", lambda e: self._bind_mousewheel(True))
        self.canvas.bind("<Leave>", lambda e: self._bind_mousewheel(False))

        if bg is not None:
            try:
                self.canvas.configure(bg=bg)
            except Exception:
                pass

    def _on_inner_configure(self, _event=None):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _on_canvas_configure(self, event=None):
        # 让 inner 宽度跟随 canvas
        try:
            self.canvas.itemconfigure(self._win, width=max(1, self.canvas.winfo_width()))
        except Exception:
            pass

    def _on_mousewheel(self, event):
        # Windows: event.delta
        delta = 0
        if hasattr(event, "delta") and event.delta:
            delta = -1 if event.delta > 0 else 1
        else:
            return
        self.canvas.yview_scroll(delta * 3, "units")
        return "break"

    def _on_mousewheel_linux(self, event):
        if event.num == 4:
            self.canvas.yview_scroll(-3, "units")
        elif event.num == 5:
            self.canvas.yview_scroll(3, "units")
        return "break"

    def _bind_mousewheel(self, bind: bool):
        w = self.winfo_toplevel()
        if bind:
            w.bind_all("<MouseWheel>", self._on_mousewheel, add="+")
            w.bind_all("<Button-4>", self._on_mousewheel_linux, add="+")
            w.bind_all("<Button-5>", self._on_mousewheel_linux, add="+")
        else:
            # 不强制解绑 all，避免影响别的区域；这里做一个轻量保护：只有进入才滚
            pass


class SnapCrop:
    # ====== 参数 ======
    MIN_CROP_SIZE = 20          # 裁剪框最小边长（image px）
    HANDLE_SIZE = 7             # 控制点半径（canvas px）
    CHECKER_CELL = 16           # 棋盘格单元格（canvas px）
    ZOOM_MIN = 0.05
    ZOOM_MAX = 12.0

    # ====== 项目信息 ======
    GITHUB_URL = "https://github.com/xuanyuanwenzhi/snapcrop"
    INFO_TAB_TITLE = "详情"

    # ====== 常见比例候选（用于“最接近比例”）======
    COMMON_RATIOS = [
        (1, 1),
        (2, 1), (3, 1), (4, 1), (5, 1),
        (1, 2), (1, 3), (1, 4), (1, 5),
        (3, 2), (2, 3),
        (4, 3), (3, 4),
        (5, 4), (4, 5),
        (5, 3), (3, 5),
        (16, 9), (9, 16),
        (21, 9), (9, 21),
        (7, 4), (4, 7),
        (8, 5), (5, 8),
        (6, 5), (5, 6),
        (7, 3), (3, 7),
        (8, 3), (3, 8),
        (10, 9), (9, 10),
    ]

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("SnapCrop")
        self.root.geometry("1260x800")
        self.root.minsize(1050, 650)

        # ====== 状态 ======
        self.image = None
        self.file_path = None
        self.scale = 1.0

        self.undo_stack = []
        self.redo_stack = []

        # canvas 显示
        self.tk_img = None
        self.canvas_img_id = None

        # 棋盘格缓存
        self._checker_cache_size = None  # (w,h)
        self._checker_cache_img = None   # PIL RGBA

        # 裁剪：图像坐标 (x1,y1,x2,y2)
        self.crop_box = None

        # 键状态
        self.shift_down = False
        self.ctrl_down = False
        self.space_down = False  # Space：临时“移动裁剪框（保持尺寸）”

        # 拖动状态
        self._drag_mode = None   # None | "new" | "move" | "resize"
        self._drag_handle = None # "nw","n","ne","w","e","sw","s","se"
        self._drag_anchor = None # (ix,iy)
        self._drag_last = None   # (ix,iy)

        # resize 时为了“中心对称”更稳：记录按下那一刻的中心
        self._resize_base_center = None  # (cx,cy) in image coords (float)
        self._resize_base_box = None

        # 裁剪 overlay
        self.crop_rect_id = None
        self.shade_ids = []
        self.handle_ids = {}

        # 画布扩展背景色（自定义）
        self.custom_bg = "#ffffff"

        # ====== 旋转链 ======
        self._rot_chain_base = None      # 本轮连续旋转的“底图”
        self._rot_chain_total_deg = 0.0  # 累计角度
        self._last_op = None             # "rotate" or others

        # ====== 分片拉伸（UI 状态）======
        self.pw_dir = tk.StringVar(value="横向（保护左右）")
        self.pw_link_other = tk.BooleanVar(value=False)  # 横向/纵向分片时：另一维是否普通缩放
        self.pw_unit = tk.StringVar(value="百分比(%)")   # 分片拉伸单位（% / px）
        self._pw_guide_ids = []                          # 分片拉伸预览线（Canvas ids）
        self._pw_guides_state = None                     # {"mode":..., "xa":..., "xb":..., "ya":..., "yb":...} in image px

        # ====== 调色（UI 状态）======
        self.var_brightness = tk.DoubleVar(value=1.0)  # 亮度系数：<1 变暗，>1 变亮
        self.var_white = tk.IntVar(value=0)            # 向白靠近强度（0~100）
        self.var_black = tk.IntVar(value=0)            # 向黑靠近强度（0~100）

        # ====== 裁剪分析（UI 状态）======
        self.crop_ratio_view_mode = tk.StringVar(value="常见比例")  # "常见比例" / "小数(小边=1)"

        # ====== 浮窗：裁剪比例/分析 ======
        self.ratio_win = None
        self._ratio_win_visible = False

        # ====== UI ======
        self._build_style()
        self._build_layout()
        self._bind_shortcuts()
        self._set_ui_enabled(False)

        # 主窗回到前台时，浮窗跟随浮上来（不做全局置顶）
        self.root.bind("<FocusIn>", self._on_root_focus_in, add="+")
        self.root.bind("<Map>", self._on_root_focus_in, add="+")

    # =========================
    # UI
    # =========================
    def _build_style(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass

        self.ACCENT = "#3b82f6"
        self.BG = "#f5f6f8"
        self.PANEL = "#ffffff"
        self.TEXT = "#111827"

        style.configure("App.TFrame", background=self.BG)
        style.configure("Panel.TFrame", background=self.PANEL)
        style.configure("Toolbar.TFrame", background=self.PANEL)

        style.configure("TLabel", font=("Segoe UI", 10), background=self.PANEL, foreground=self.TEXT)
        style.configure("AppTitle.TLabel", font=("Segoe UI", 11, "bold"), background=self.PANEL, foreground=self.TEXT)

        style.configure("TButton", font=("Segoe UI", 10), padding=(10, 6))
        style.configure("Tool.TButton", font=("Segoe UI", 10), padding=(10, 6))

        style.configure("Accent.TButton", font=("Segoe UI", 10, "bold"), padding=(10, 6),
                        background=self.ACCENT, foreground="white")
        style.map("Accent.TButton",
                  background=[("active", "#2563eb"), ("disabled", "#93c5fd")],
                  foreground=[("disabled", "#f8fafc")])

        style.configure("TLabelframe", background=self.PANEL)
        style.configure("TLabelframe.Label", background=self.PANEL, font=("Segoe UI", 10, "bold"))

        style.configure("TEntry", padding=(6, 4))
        style.configure("TCombobox", padding=(6, 4))

    def _build_layout(self):
        root = self.root
        root.configure(background=self.BG)

        # 顶部工具条
        self.toolbar = ttk.Frame(root, style="Toolbar.TFrame")
        self.toolbar.pack(side=tk.TOP, fill=tk.X, padx=10, pady=(10, 8))

        ttk.Label(self.toolbar, text="SnapCrop", style="AppTitle.TLabel").pack(side=tk.LEFT, padx=(10, 16))

        self.btn_open = ttk.Button(self.toolbar, text="打开 (Ctrl+O)", style="Tool.TButton", command=self.open_image)
        self.btn_open.pack(side=tk.LEFT, padx=6)

        self.btn_save = ttk.Button(self.toolbar, text="保存 (Ctrl+S)", style="Tool.TButton", command=self.save_image)
        self.btn_save.pack(side=tk.LEFT, padx=6)

        self.btn_undo = ttk.Button(self.toolbar, text="撤销 (Ctrl+Z)", style="Tool.TButton", command=self.undo)
        self.btn_undo.pack(side=tk.LEFT, padx=6)

        self.btn_redo = ttk.Button(self.toolbar, text="重做 (Ctrl+Y)", style="Tool.TButton", command=self.redo)
        self.btn_redo.pack(side=tk.LEFT, padx=6)

        ttk.Separator(self.toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=10)

        self.btn_fit = ttk.Button(self.toolbar, text="适配窗口", style="Tool.TButton", command=self.fit_to_view)
        self.btn_fit.pack(side=tk.LEFT, padx=6)

        self.btn_100 = ttk.Button(self.toolbar, text="100%", style="Tool.TButton", command=self.zoom_100)
        self.btn_100.pack(side=tk.LEFT, padx=6)

        ttk.Separator(self.toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=10)

        self.btn_apply_crop = ttk.Button(self.toolbar, text="应用裁剪 (Enter)", style="Accent.TButton", command=self.apply_crop)
        self.btn_apply_crop.pack(side=tk.LEFT, padx=6)

        self.btn_clear_crop = ttk.Button(self.toolbar, text="清除裁剪 (Esc)", style="Tool.TButton", command=self.clear_crop)
        self.btn_clear_crop.pack(side=tk.LEFT, padx=6)

        ttk.Separator(self.toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=10)

        self.btn_ratio_panel = ttk.Button(
            self.toolbar, text="裁剪面板 (F4)", style="Tool.TButton", command=self.toggle_ratio_window
        )
        self.btn_ratio_panel.pack(side=tk.LEFT, padx=6)

        # 主体：左面板 + 右 canvas（用 PanedWindow 可拉伸）
        self.main = ttk.Frame(root, style="App.TFrame")
        self.main.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        self.paned = ttk.Panedwindow(self.main, orient=tk.HORIZONTAL)
        self.paned.pack(fill=tk.BOTH, expand=True)

        self.left = ttk.Frame(self.paned, style="Panel.TFrame", width=360)
        self.right = ttk.Frame(self.paned, style="Panel.TFrame")

        self.paned.add(self.left, weight=0)   # 左侧固定偏重（但可拖动）
        self.paned.add(self.right, weight=1)

        self.left.pack_propagate(False)

        # 左：Notebook（每个 tab 可滚动）
        self.nb = ttk.Notebook(self.left)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        self.tab_transform = ScrollableFrame(self.nb, bg=self.PANEL)
        self.tab_crop = ScrollableFrame(self.nb, bg=self.PANEL)
        self.tab_split = ScrollableFrame(self.nb, bg=self.PANEL)
        self.tab_adjust = ScrollableFrame(self.nb, bg=self.PANEL)
        self.tab_ops = ScrollableFrame(self.nb, bg=self.PANEL)
        self.tab_info = ScrollableFrame(self.nb, bg=self.PANEL)

        self.nb.add(self.tab_transform, text="缩放")
        self.nb.add(self.tab_crop, text="裁剪")
        self.nb.add(self.tab_ops, text="变换")
        self.nb.add(self.tab_split, text="分割")
        self.nb.add(self.tab_adjust, text="调色")
        self.nb.add(self.tab_info, text=self.INFO_TAB_TITLE)

        # 下面开始：把你原来所有 “self.tab_xxx” 当 parent 的地方，改成 “self.tab_xxx.inner”
        # ---- Transform ----
        lf = ttk.Labelframe(self.tab_transform.inner, text="缩放 / 拉伸")
        lf.pack(fill=tk.X, padx=10, pady=10)

        row = ttk.Frame(lf)
        row.pack(fill=tk.X, pady=(8, 6))
        ttk.Label(row, text="宽(px)").pack(side=tk.LEFT)
        self.ent_w = ttk.Entry(row, width=10)
        self.ent_w.pack(side=tk.LEFT, padx=(6, 12))
        ttk.Label(row, text="高(px)").pack(side=tk.LEFT)
        self.ent_h = ttk.Entry(row, width=10)
        self.ent_h.pack(side=tk.LEFT, padx=(6, 0))

        self.lock_ratio_resize = tk.BooleanVar(value=True)
        ttk.Checkbutton(lf, text="锁定等比例（缩放）", variable=self.lock_ratio_resize).pack(anchor=tk.W, padx=2, pady=(0, 6))

        row2 = ttk.Frame(lf)
        row2.pack(fill=tk.X, pady=(0, 8))
        self.btn_apply_resize = ttk.Button(row2, text="应用缩放", command=self.apply_resize, style="Accent.TButton")
        self.btn_apply_resize.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_apply_stretch = ttk.Button(row2, text="自由拉伸", command=self.apply_stretch, style="Tool.TButton")
        self.btn_apply_stretch.pack(side=tk.LEFT)

        # ---- Piecewise Stretch ----
        lf_pw = ttk.Labelframe(self.tab_transform.inner, text="分片拉伸（保护边缘/圆角）")
        lf_pw.pack(fill=tk.X, padx=10, pady=(0, 10))

        rowpw1 = ttk.Frame(lf_pw)
        rowpw1.pack(fill=tk.X, padx=8, pady=(10, 6))
        ttk.Label(rowpw1, text="方向").pack(side=tk.LEFT)
        self.combo_pw_dir = ttk.Combobox(
            rowpw1, textvariable=self.pw_dir, state="readonly", width=18,
            values=("横向（保护左右）", "纵向（保护上下）", "双向（九宫格）")
        )
        self.combo_pw_dir.pack(side=tk.LEFT, padx=(8, 8))

        ttk.Label(rowpw1, text="单位").pack(side=tk.LEFT, padx=(8, 0))
        self.combo_pw_unit = ttk.Combobox(
            rowpw1, textvariable=self.pw_unit, state="readonly", width=10,
            values=("百分比(%)", "像素(px)")
        )
        self.combo_pw_unit.pack(side=tk.LEFT, padx=(8, 8))
        self.combo_pw_unit.bind("<<ComboboxSelected>>", self._on_pw_unit_change)

        self.chk_pw_link = ttk.Checkbutton(
            rowpw1, text="双向（普通缩放）", variable=self.pw_link_other
        )
        self.chk_pw_link.pack(side=tk.LEFT)

        # 横向范围（百分比/像素）
        rowpw2 = ttk.Frame(lf_pw)
        rowpw2.pack(fill=tk.X, padx=8, pady=(0, 6))
        self.lbl_pw_x = ttk.Label(rowpw2, text="横向拉伸区域(%)")
        self.lbl_pw_x.pack(side=tk.LEFT)
        self.ent_pw_x1 = ttk.Entry(rowpw2, width=6)
        self.ent_pw_x2 = ttk.Entry(rowpw2, width=6)
        self.ent_pw_x1.pack(side=tk.LEFT, padx=(8, 6))
        ttk.Label(rowpw2, text="~").pack(side=tk.LEFT)
        self.ent_pw_x2.pack(side=tk.LEFT, padx=(6, 0))
        self.ent_pw_x1.insert(0, "20")
        self.ent_pw_x2.insert(0, "80")

        # 纵向范围（百分比/像素）
        rowpw3 = ttk.Frame(lf_pw)
        rowpw3.pack(fill=tk.X, padx=8, pady=(0, 6))
        self.lbl_pw_y = ttk.Label(rowpw3, text="纵向拉伸区域(%)")
        self.lbl_pw_y.pack(side=tk.LEFT)
        self.ent_pw_y1 = ttk.Entry(rowpw3, width=6)
        self.ent_pw_y2 = ttk.Entry(rowpw3, width=6)
        self.ent_pw_y1.pack(side=tk.LEFT, padx=(8, 6))
        ttk.Label(rowpw3, text="~").pack(side=tk.LEFT)
        self.ent_pw_y2.pack(side=tk.LEFT, padx=(6, 0))
        self.ent_pw_y1.insert(0, "20")
        self.ent_pw_y2.insert(0, "80")

        ttk.Label(
            lf_pw,
            text="说明：\n"
                 "- 横向：左右边缘保持不变形，仅拉伸中间区域（常用于圆角框）\n"
                 "- 纵向：上下边缘保持不变形，仅拉伸中间区域\n"
                 "- 双向：九宫格拉伸（角不变、边单轴拉伸、中间双轴拉伸）\n"
                 "- 横向/纵向模式下：默认只改一个方向；勾选“同时调整另一边”才会把另一维用普通缩放改到目标尺寸\n"
                 "- 预览：横/纵显示 2 条虚线；双向显示 4 条虚线\n",
            justify=tk.LEFT
        ).pack(fill=tk.X, padx=8, pady=(0, 6))

        rowpw_btn = ttk.Frame(lf_pw)
        rowpw_btn.pack(fill=tk.X, padx=8, pady=(0, 6))
        self.btn_piecewise_preview = ttk.Button(
            rowpw_btn, text="预览分割线", command=self.preview_piecewise_guides, style="Tool.TButton"
        )
        self.btn_piecewise_preview.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_piecewise_clear_preview = ttk.Button(
            rowpw_btn, text="清除预览", command=self.clear_piecewise_guides, style="Tool.TButton"
        )
        self.btn_piecewise_clear_preview.pack(side=tk.LEFT)

        self.btn_piecewise = ttk.Button(
            lf_pw, text="应用分片拉伸", command=self.apply_piecewise_stretch, style="Accent.TButton"
        )
        self.btn_piecewise.pack(fill=tk.X, padx=8, pady=(0, 10))

        # ---- Crop (tab) ----
        # 裁剪页：给一个入口按钮（比例/分析在浮窗里）
        lf_crop_entry = ttk.Labelframe(self.tab_crop.inner, text="裁剪面板（浮窗）")
        lf_crop_entry.pack(fill=tk.X, padx=10, pady=(10, 6))
        ttk.Label(
            lf_crop_entry,
            text="提示：比例设置 + 裁剪分析 已移到可拖动浮窗。\n按 F4 或点按钮打开。",
            justify=tk.LEFT
        ).pack(anchor=tk.W, padx=8, pady=(8, 6))
        ttk.Button(
            lf_crop_entry, text="打开/隐藏裁剪面板 (F4)", command=self.toggle_ratio_window, style="Accent.TButton"
        ).pack(fill=tk.X, padx=8, pady=(0, 10))

        ttk.Label(
            self.tab_crop.inner,
            text="比例手感：\n"
                 "- 固定比例时，拖动边(N/S/E/W)默认“以中心对称缩放”（更像PS）\n"
                 "- Shift：自由模式下临时 1:1；已有框时临时保持当前比例\n"
                 "- Space：拖拽边/角时临时“移动裁剪框（保持尺寸）”（用于卡边时顺滑挪动）\n"
                 "- 方向键：移动（Shift=10px）\n"
                 "- Ctrl + 方向键：向外扩展；Ctrl+Shift+方向键：向内收缩\n"
                 "- Enter：应用裁剪；Esc：清除裁剪框\n"
                 "- 滚轮：缩放；中键/右键拖拽：平移\n",
            justify=tk.LEFT
        ).pack(fill=tk.X, padx=12, pady=(6, 10))

        lf2 = ttk.Labelframe(self.tab_crop.inner, text="边缘裁剪（px / %）")
        lf2.pack(fill=tk.X, padx=10, pady=(0, 10))

        grid = ttk.Frame(lf2)
        grid.pack(fill=tk.X, pady=8, padx=8)

        def mk_entry(lbl, r, c):
            ttk.Label(grid, text=lbl).grid(row=r, column=c, sticky="w", padx=(0, 6), pady=4)
            e = ttk.Entry(grid, width=10)
            e.grid(row=r, column=c + 1, sticky="w", pady=4)
            return e

        self.ent_top = mk_entry("上", 0, 0)
        self.ent_bottom = mk_entry("下", 1, 0)
        self.ent_left = mk_entry("左", 0, 2)
        self.ent_right = mk_entry("右", 1, 2)

        for i in range(4):
            grid.columnconfigure(i, weight=1)

        row3 = ttk.Frame(lf2)
        row3.pack(fill=tk.X, pady=(0, 8), padx=8)
        self.btn_edge_crop = ttk.Button(row3, text="生成裁剪框", command=self.edge_crop_preview, style="Tool.TButton")
        self.btn_edge_crop.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_apply_all = ttk.Button(row3, text="应用裁剪 + 缩放", command=self.apply_crop_and_resize, style="Accent.TButton")
        self.btn_apply_all.pack(side=tk.LEFT)

        # ---- Crop by size ----
        lf_sizecrop = ttk.Labelframe(self.tab_crop.inner, text="按尺寸生成裁剪框（px）")
        lf_sizecrop.pack(fill=tk.X, padx=10, pady=(0, 10))

        rowsc = ttk.Frame(lf_sizecrop)
        rowsc.pack(fill=tk.X, padx=8, pady=(10, 6))
        ttk.Label(rowsc, text="宽").pack(side=tk.LEFT)
        self.ent_crop_w = ttk.Entry(rowsc, width=10)
        self.ent_crop_w.pack(side=tk.LEFT, padx=(6, 12))
        ttk.Label(rowsc, text="高").pack(side=tk.LEFT)
        self.ent_crop_h = ttk.Entry(rowsc, width=10)
        self.ent_crop_h.pack(side=tk.LEFT, padx=(6, 0))

        self.btn_crop_by_size = ttk.Button(
            lf_sizecrop, text="生成居中裁剪框", command=self.crop_box_by_size_preview, style="Accent.TButton"
        )
        self.btn_crop_by_size.pack(fill=tk.X, padx=8, pady=(0, 10))

        # ---- Ops (Rotate/Flip/Canvas/Trim) ----
        lf_rot = ttk.Labelframe(self.tab_ops.inner, text="旋转")
        lf_rot.pack(fill=tk.X, padx=10, pady=(10, 8))

        rowrot = ttk.Frame(lf_rot)
        rowrot.pack(fill=tk.X, padx=8, pady=8)

        ttk.Label(rowrot, text="角度(°)").pack(side=tk.LEFT)
        self.ent_deg = ttk.Entry(rowrot, width=8)
        self.ent_deg.pack(side=tk.LEFT, padx=(8, 12))
        self.ent_deg.insert(0, "0")

        self.btn_rot_apply = ttk.Button(rowrot, text="应用旋转", command=self.rotate_by_entry, style="Accent.TButton")
        self.btn_rot_apply.pack(side=tk.LEFT, padx=(0, 8))

        self.btn_rot_l = ttk.Button(rowrot, text="⟲ 90°", command=lambda: self.rotate_quick(90), style="Tool.TButton")
        self.btn_rot_l.pack(side=tk.LEFT, padx=(0, 6))
        self.btn_rot_r = ttk.Button(rowrot, text="⟳ 90°", command=lambda: self.rotate_quick(-90), style="Tool.TButton")
        self.btn_rot_r.pack(side=tk.LEFT, padx=(0, 6))
        self.btn_rot_180 = ttk.Button(rowrot, text="180°", command=lambda: self.rotate_quick(180), style="Tool.TButton")
        self.btn_rot_180.pack(side=tk.LEFT)

        lf_flip = ttk.Labelframe(self.tab_ops.inner, text="翻转")
        lf_flip.pack(fill=tk.X, padx=10, pady=(0, 8))

        rowf = ttk.Frame(lf_flip)
        rowf.pack(fill=tk.X, padx=8, pady=8)
        self.btn_flip_h = ttk.Button(rowf, text="水平翻转", command=self.flip_horizontal, style="Tool.TButton")
        self.btn_flip_h.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_flip_v = ttk.Button(rowf, text="垂直翻转", command=self.flip_vertical, style="Tool.TButton")
        self.btn_flip_v.pack(side=tk.LEFT)

        # ---- Canvas Expand ----
        lf_canvas = ttk.Labelframe(self.tab_ops.inner, text="画布扩展（Padding px）")
        lf_canvas.pack(fill=tk.X, padx=10, pady=(0, 8))

        grid2 = ttk.Frame(lf_canvas)
        grid2.pack(fill=tk.X, padx=8, pady=8)

        grid2.columnconfigure(0, weight=0)
        grid2.columnconfigure(1, weight=1)
        grid2.columnconfigure(2, weight=0)
        grid2.columnconfigure(3, weight=1)

        def mk_pad(lbl, r, c, default="0"):
            ttk.Label(grid2, text=lbl).grid(row=r, column=c, sticky="w", padx=(0, 6), pady=4)
            e = ttk.Entry(grid2, width=6)
            e.grid(row=r, column=c + 1, sticky="ew", padx=(0, 10), pady=4)
            e.insert(0, default)
            return e

        self.ent_pad_top = mk_pad("上", 0, 0)
        self.ent_pad_left = mk_pad("左", 0, 2)
        self.ent_pad_bottom = mk_pad("下", 1, 0)
        self.ent_pad_right = mk_pad("右", 1, 2)

        ttk.Label(grid2, text="背景").grid(row=2, column=0, sticky="w", pady=(10, 4))
        self.bg_mode = tk.StringVar(value="透明(如有Alpha)")
        self.combo_bg = ttk.Combobox(
            grid2, textvariable=self.bg_mode, state="readonly",
            values=("透明(如有Alpha)", "白色", "黑色", "自定义颜色")
        )
        self.combo_bg.grid(row=2, column=1, columnspan=3, sticky="ew", pady=(10, 4))

        self.btn_pick_bg = ttk.Button(grid2, text="选颜色", command=self.pick_bg_color, style="Tool.TButton")
        self.btn_pick_bg.grid(row=3, column=0, columnspan=4, sticky="e", pady=(0, 6))

        self.btn_expand = ttk.Button(lf_canvas, text="应用扩展画布", command=self.expand_canvas, style="Accent.TButton")
        self.btn_expand.pack(fill=tk.X, padx=8, pady=(0, 10))

        lf_trim = ttk.Labelframe(self.tab_ops.inner, text="自动修剪")
        lf_trim.pack(fill=tk.X, padx=10, pady=(0, 10))

        self.btn_trim_alpha = ttk.Button(lf_trim, text="自动修剪透明边（Trim Alpha）", command=self.trim_transparent, style="Accent.TButton")
        self.btn_trim_alpha.pack(fill=tk.X, padx=8, pady=10)

        # ---- Split ----
        lf3 = ttk.Labelframe(self.tab_split.inner, text="等分分割")
        lf3.pack(fill=tk.X, padx=10, pady=10)

        self.split_mode = tk.StringVar(value="4等分（2×2）")
        self.combo_split = ttk.Combobox(
            lf3, textvariable=self.split_mode, state="readonly",
            values=("4等分（2×2）", "9等分（3×3）", "16等分（4×4）", "自定义行列")
        )
        self.combo_split.pack(fill=tk.X, padx=8, pady=(10, 6))
        self.combo_split.bind("<<ComboboxSelected>>", self._on_split_mode)

        self.custom_split = ttk.Frame(lf3)
        self.ent_rows = ttk.Entry(self.custom_split, width=6)
        self.ent_cols = ttk.Entry(self.custom_split, width=6)
        ttk.Label(self.custom_split, text="行").pack(side=tk.LEFT)
        self.ent_rows.pack(side=tk.LEFT, padx=(6, 14))
        ttk.Label(self.custom_split, text="列").pack(side=tk.LEFT)
        self.ent_cols.pack(side=tk.LEFT, padx=(6, 0))

        self.btn_split = ttk.Button(lf3, text="执行分割并保存", command=self.split_image, style="Accent.TButton")
        self.btn_split.pack(fill=tk.X, padx=8, pady=(10, 10))

        # ---- Adjust (Color) ----
        lf_adj1 = ttk.Labelframe(self.tab_adjust.inner, text="亮度（不影响透明区域）")
        lf_adj1.pack(fill=tk.X, padx=10, pady=(10, 8))

        rowa = ttk.Frame(lf_adj1)
        rowa.pack(fill=tk.X, padx=8, pady=(10, 6))
        ttk.Label(rowa, text="亮度系数").pack(side=tk.LEFT)

        self.scale_bri = ttk.Scale(rowa, from_=0.2, to=2.0, variable=self.var_brightness)
        self.scale_bri.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 8))

        self.lbl_bri = ttk.Label(rowa, text="1.00")
        self.lbl_bri.pack(side=tk.RIGHT)

        def _sync_bri_label(*_):
            try:
                self.lbl_bri.config(text=f"{float(self.var_brightness.get()):.2f}")
            except Exception:
                self.lbl_bri.config(text="1.00")

        self.var_brightness.trace_add("write", _sync_bri_label)
        _sync_bri_label()

        rowa2 = ttk.Frame(lf_adj1)
        rowa2.pack(fill=tk.X, padx=8, pady=(0, 10))
        self.btn_apply_bri = ttk.Button(rowa2, text="应用亮度", command=self.apply_brightness, style="Accent.TButton")
        self.btn_apply_bri.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_reset_bri = ttk.Button(rowa2, text="重置为 1.00", command=lambda: self.var_brightness.set(1.0), style="Tool.TButton")
        self.btn_reset_bri.pack(side=tk.LEFT)

        lf_adj2 = ttk.Labelframe(self.tab_adjust.inner, text="变白 / 变黑（混合，不影响透明区域）")
        lf_adj2.pack(fill=tk.X, padx=10, pady=(0, 10))

        roww = ttk.Frame(lf_adj2)
        roww.pack(fill=tk.X, padx=8, pady=(10, 6))
        ttk.Label(roww, text="变白强度").pack(side=tk.LEFT)
        self.scale_white = ttk.Scale(roww, from_=0, to=100, variable=self.var_white)
        self.scale_white.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 8))
        self.lbl_white = ttk.Label(roww, text="0%")
        self.lbl_white.pack(side=tk.RIGHT)

        def _sync_white_label(*_):
            try:
                self.lbl_white.config(text=f"{int(float(self.var_white.get()))}%")
            except Exception:
                self.lbl_white.config(text="0%")

        self.var_white.trace_add("write", _sync_white_label)
        _sync_white_label()

        rowb = ttk.Frame(lf_adj2)
        rowb.pack(fill=tk.X, padx=8, pady=(0, 6))
        ttk.Label(rowb, text="变黑强度").pack(side=tk.LEFT)
        self.scale_black = ttk.Scale(rowb, from_=0, to=100, variable=self.var_black)
        self.scale_black.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 8))
        self.lbl_black = ttk.Label(rowb, text="0%")
        self.lbl_black.pack(side=tk.RIGHT)

        def _sync_black_label(*_):
            try:
                self.lbl_black.config(text=f"{int(float(self.var_black.get()))}%")
            except Exception:
                self.lbl_black.config(text="0%")

        self.var_black.trace_add("write", _sync_black_label)
        _sync_black_label()

        rowwb = ttk.Frame(lf_adj2)
        rowwb.pack(fill=tk.X, padx=8, pady=(0, 10))
        self.btn_apply_white = ttk.Button(rowwb, text="应用变白", command=self.apply_whiten, style="Accent.TButton")
        self.btn_apply_white.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_apply_black = ttk.Button(rowwb, text="应用变黑", command=self.apply_blacken, style="Tool.TButton")
        self.btn_apply_black.pack(side=tk.LEFT)

        ttk.Label(
            self.tab_adjust.inner,
            text="提示：\n"
                 "- 亮度：系数 < 1 变暗，> 1 变亮\n"
                 "- 变白/变黑：把 RGB 向白/黑“混合靠近”，透明部分不受影响\n",
            justify=tk.LEFT
        ).pack(fill=tk.X, padx=12, pady=(0, 8))

        # ---- Info / Details ----
        self._build_info_tab()

        # 右：Canvas + Scrollbars
        canvas_wrap = ttk.Frame(self.right, style="Panel.TFrame")
        canvas_wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        self.hbar = ttk.Scrollbar(canvas_wrap, orient=tk.HORIZONTAL)
        self.vbar = ttk.Scrollbar(canvas_wrap, orient=tk.VERTICAL)

        self.canvas = tk.Canvas(
            canvas_wrap, bg="#ffffff", highlightthickness=0,
            xscrollcommand=self.hbar.set, yscrollcommand=self.vbar.set
        )
        self.hbar.config(command=self.canvas.xview)
        self.vbar.config(command=self.canvas.yview)

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.vbar.grid(row=0, column=1, sticky="ns")
        self.hbar.grid(row=1, column=0, sticky="ew")

        canvas_wrap.rowconfigure(0, weight=1)
        canvas_wrap.columnconfigure(0, weight=1)

        # 状态栏
        self.status = ttk.Frame(root, style="Toolbar.TFrame")
        self.status.pack(side=tk.BOTTOM, fill=tk.X, padx=10, pady=(0, 10))
        self.lbl_status = ttk.Label(self.status, text="未打开图片", background=self.PANEL)
        self.lbl_status.pack(side=tk.LEFT, padx=10)
        self.lbl_zoom = ttk.Label(self.status, text="缩放：100%", background=self.PANEL)
        self.lbl_zoom.pack(side=tk.RIGHT, padx=10)

        # Canvas 绑定
        self._bind_canvas_events()

        # 初始化单位显示（避免初始文本不一致）
        self._on_pw_unit_change()

        # 初始化裁剪分析（无裁剪框）
        self._update_crop_analysis()

    def _build_info_tab(self):
        lf = ttk.Labelframe(self.tab_info.inner, text="项目 / Project")
        lf.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        ttk.Label(
            lf,
            text="SnapCrop 是一个开源的桌面图片裁剪与编辑工具。\n"
                 "你可以在 GitHub 上查看源码、提交 Issue、或参与改进。",
            justify=tk.LEFT
        ).pack(anchor=tk.W, padx=10, pady=(10, 8))

        row = ttk.Frame(lf)
        row.pack(fill=tk.X, padx=10, pady=(0, 8))

        ttk.Label(row, text="GitHub：").pack(side=tk.LEFT)

        self._github_var = tk.StringVar(value=self.GITHUB_URL)
        ent = ttk.Entry(row, textvariable=self._github_var, state="readonly")
        ent.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 8))

        self.btn_open_github = ttk.Button(row, text="打开网页", command=self.open_github, style="Accent.TButton")
        self.btn_open_github.pack(side=tk.RIGHT)

        ttk.Label(
            lf,
            text="说明：该项目已开源，欢迎 Star / Fork / 提 Issue。",
            justify=tk.LEFT
        ).pack(anchor=tk.W, padx=10, pady=(0, 10))

    # =========================
    # 浮窗：裁剪比例 + 裁剪分析
    # =========================
    def _create_ratio_window_if_needed(self):
        if self.ratio_win and self.ratio_win.winfo_exists():
            return

        win = tk.Toplevel(self.root)
        self.ratio_win = win
        win.title("裁剪面板（比例 / 分析）")
        win.geometry("380x520")
        win.minsize(320, 420)

        # Windows：尽量不单独出任务栏
        try:
            win.transient(self.root)
        except Exception:
            pass
        try:
            win.wm_attributes("-toolwindow", True)
        except Exception:
            pass

        # 关闭按钮：改为隐藏
        win.protocol("WM_DELETE_WINDOW", self.hide_ratio_window)

        # 内容
        container = ttk.Frame(win, style="Panel.TFrame")
        container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # 裁剪比例
        lf_ratio = ttk.Labelframe(container, text="裁剪比例")
        lf_ratio.pack(fill=tk.X, padx=0, pady=(0, 10))

        rowr = ttk.Frame(lf_ratio)
        rowr.pack(fill=tk.X, pady=8, padx=8)

        ttk.Label(rowr, text="固定比例").pack(side=tk.LEFT)
        self.aspect_mode = tk.StringVar(value="自由")
        self.combo_aspect = ttk.Combobox(
            rowr, textvariable=self.aspect_mode, state="readonly", width=14,
            values=("自由", "1:1", "16:9", "9:16", "4:3", "3:4", "3:2", "2:3", "自定义")
        )
        self.combo_aspect.pack(side=tk.LEFT, padx=(8, 8))
        self.combo_aspect.bind("<<ComboboxSelected>>", self._on_aspect_mode)

        self.aspect_custom_frame = ttk.Frame(lf_ratio)
        self.ent_aspect_w = ttk.Entry(self.aspect_custom_frame, width=6)
        self.ent_aspect_h = ttk.Entry(self.aspect_custom_frame, width=6)
        ttk.Label(self.aspect_custom_frame, text="W").pack(side=tk.LEFT)
        self.ent_aspect_w.pack(side=tk.LEFT, padx=(6, 10))
        ttk.Label(self.aspect_custom_frame, text="H").pack(side=tk.LEFT)
        self.ent_aspect_h.pack(side=tk.LEFT, padx=(6, 0))

        ttk.Button(
            lf_ratio, text="清除固定比例（切回自由）", style="Tool.TButton",
            command=lambda: self._set_aspect_free()
        ).pack(fill=tk.X, padx=8, pady=(0, 10))

        # 裁剪分析
        lf_an = ttk.Labelframe(container, text="裁剪分析（实时）")
        lf_an.pack(fill=tk.X, padx=0, pady=(0, 10))

        rowan = ttk.Frame(lf_an)
        rowan.pack(fill=tk.X, padx=8, pady=(10, 6))
        ttk.Label(rowan, text="比例显示").pack(side=tk.LEFT)

        self.combo_crop_ratio_view = ttk.Combobox(
            rowan, textvariable=self.crop_ratio_view_mode, state="readonly", width=16,
            values=("常见比例", "小数(小边=1)")
        )
        self.combo_crop_ratio_view.pack(side=tk.LEFT, padx=(8, 0))
        self.combo_crop_ratio_view.bind("<<ComboboxSelected>>", lambda e: self._update_crop_analysis())

        self.var_an_size = tk.StringVar(value="当前裁剪：-")
        self.var_an_reduce = tk.StringVar(value="已约分：-")
        self.var_an_near = tk.StringVar(value="")
        self.var_an_perfect = tk.StringVar(value="")
        self.var_an_k = tk.StringVar(value="")
        self.var_an_decimal = tk.StringVar(value="")
        self.var_an_multi = tk.StringVar(value="2/4 倍数：-")
        self.var_an_pow2 = tk.StringVar(value="2 的次幂：-")

        ttk.Label(lf_an, textvariable=self.var_an_size, justify=tk.LEFT).pack(anchor=tk.W, padx=8, pady=(0, 2))
        ttk.Label(lf_an, textvariable=self.var_an_reduce, justify=tk.LEFT).pack(anchor=tk.W, padx=8, pady=(0, 2))

        self.lbl_an_near = ttk.Label(lf_an, textvariable=self.var_an_near, justify=tk.LEFT)
        self.lbl_an_perfect = ttk.Label(lf_an, textvariable=self.var_an_perfect, justify=tk.LEFT)
        self.lbl_an_k = ttk.Label(lf_an, textvariable=self.var_an_k, justify=tk.LEFT)
        self.lbl_an_decimal = ttk.Label(lf_an, textvariable=self.var_an_decimal, justify=tk.LEFT)

        self.lbl_an_near.pack(anchor=tk.W, padx=8, pady=(0, 2))
        self.lbl_an_perfect.pack(anchor=tk.W, padx=8, pady=(0, 2))
        self.lbl_an_k.pack(anchor=tk.W, padx=8, pady=(0, 2))
        self.lbl_an_decimal.pack_forget()

        ttk.Label(lf_an, textvariable=self.var_an_multi, justify=tk.LEFT).pack(anchor=tk.W, padx=8, pady=(6, 2))
        ttk.Label(lf_an, textvariable=self.var_an_pow2, justify=tk.LEFT).pack(anchor=tk.W, padx=8, pady=(0, 10))

        # 底部快捷提示
        ttk.Label(
            container,
            text="提示：主窗口回到前台时，本面板会自动浮上来。\n关闭面板=隐藏，不会销毁。",
            justify=tk.LEFT
        ).pack(fill=tk.X, padx=2, pady=(0, 0))

        self._update_crop_analysis()

    def _set_aspect_free(self):
        try:
            self.aspect_mode.set("自由")
        except Exception:
            pass
        try:
            self.aspect_custom_frame.pack_forget()
        except Exception:
            pass
        if self.image and self.crop_box:
            self._update_crop_overlay()

    def toggle_ratio_window(self):
        if self._ratio_win_visible:
            self.hide_ratio_window()
        else:
            self.show_ratio_window()

    def show_ratio_window(self):
        self._create_ratio_window_if_needed()
        if not (self.ratio_win and self.ratio_win.winfo_exists()):
            return
        self._ratio_win_visible = True
        try:
            self.ratio_win.deiconify()
        except Exception:
            pass
        self._lift_ratio_window()
        self._update_crop_analysis()

    def hide_ratio_window(self):
        if self.ratio_win and self.ratio_win.winfo_exists():
            try:
                self.ratio_win.withdraw()
            except Exception:
                pass
        self._ratio_win_visible = False
        self._return_focus_to_canvas()

    def _lift_ratio_window(self):
        if not (self.ratio_win and self.ratio_win.winfo_exists()):
            return
        if not self._ratio_win_visible:
            return
        # 关键：只在主窗口回到前台时把它提上来，不做全局置顶
        try:
            self.ratio_win.lift()
        except Exception:
            pass
        try:
            self.ratio_win.attributes("-topmost", True)
            self.ratio_win.after(30, lambda: self._safe_unset_topmost())
        except Exception:
            pass

    def _safe_unset_topmost(self):
        if self.ratio_win and self.ratio_win.winfo_exists():
            try:
                self.ratio_win.attributes("-topmost", False)
            except Exception:
                pass

    def _on_root_focus_in(self, _event=None):
        self._lift_ratio_window()

    # =========================
    # Focus：避免“点两下”
    # =========================
    def _return_focus_to_canvas(self):
        try:
            if self.canvas and self.canvas.winfo_exists():
                self.canvas.focus_set()
        except Exception:
            pass

    # =========================
    # Canvas 绑定、快捷键等
    # =========================
    def open_github(self):
        try:
            webbrowser.open_new_tab(self.GITHUB_URL)
        except Exception as e:
            messagebox.showerror("错误", f"无法打开浏览器：{e}")

    def _bind_canvas_events(self):
        c = self.canvas
        c.bind("<ButtonPress-1>", self._on_lmb_down)
        c.bind("<B1-Motion>", self._on_lmb_drag)
        c.bind("<ButtonRelease-1>", self._on_lmb_up)
        c.bind("<Motion>", self._on_mouse_move)

        c.bind("<ButtonPress-2>", self._on_pan_start)
        c.bind("<B2-Motion>", self._on_pan_drag)
        c.bind("<ButtonPress-3>", self._on_pan_start)
        c.bind("<B3-Motion>", self._on_pan_drag)

        c.bind("<MouseWheel>", self._on_wheel)      # Win/mac
        c.bind("<Button-4>", self._on_wheel_linux)  # Linux
        c.bind("<Button-5>", self._on_wheel_linux)

        c.bind("<Configure>", lambda e: self._update_status())

        # Space 只在 Canvas 上生效，并在失焦时强制释放
        c.configure(takefocus=True)
        c.bind("<KeyPress-space>", self._on_space_press)
        c.bind("<KeyRelease-space>", self._on_space_release)
        c.bind("<FocusOut>", lambda e: self._force_release_space())

    def _bind_shortcuts(self):
        r = self.root
        r.bind("<Control-o>", lambda e: self.open_image())
        r.bind("<Control-s>", lambda e: self.save_image())
        r.bind("<Control-z>", lambda e: self.undo())
        r.bind("<Control-y>", lambda e: self.redo())
        r.bind("<Escape>", lambda e: self.clear_crop())
        r.bind("<Return>", lambda e: self.apply_crop())

        r.bind("<KeyPress-Shift_L>", lambda e: self._set_shift(True))
        r.bind("<KeyRelease-Shift_L>", lambda e: self._set_shift(False))
        r.bind("<KeyPress-Shift_R>", lambda e: self._set_shift(True))
        r.bind("<KeyRelease-Shift_R>", lambda e: self._set_shift(False))

        r.bind("<KeyPress-Control_L>", lambda e: self._set_ctrl(True))
        r.bind("<KeyRelease-Control_L>", lambda e: self._set_ctrl(False))
        r.bind("<KeyPress-Control_R>", lambda e: self._set_ctrl(True))
        r.bind("<KeyRelease-Control_R>", lambda e: self._set_ctrl(False))

        r.bind("<Up>", lambda e: self._on_arrow("Up"))
        r.bind("<Down>", lambda e: self._on_arrow("Down"))
        r.bind("<Left>", lambda e: self._on_arrow("Left"))
        r.bind("<Right>", lambda e: self._on_arrow("Right"))

        # 浮窗快捷键
        r.bind("<F4>", lambda e: self.toggle_ratio_window())

    def _set_shift(self, v: bool):
        self.shift_down = v

    def _set_ctrl(self, v: bool):
        self.ctrl_down = v

    def _on_space_press(self, event):
        self.space_down = True
        return "break"

    def _on_space_release(self, event):
        self.space_down = False
        return "break"

    def _force_release_space(self):
        self.space_down = False

    def _set_ui_enabled(self, enabled: bool):
        st = "normal" if enabled else "disabled"
        for w in [
            self.btn_save, self.btn_undo, self.btn_redo, self.btn_fit, self.btn_100,
            self.btn_apply_crop, self.btn_clear_crop,
            self.btn_apply_resize, self.btn_apply_stretch, self.btn_edge_crop, self.btn_apply_all, self.btn_split,
            self.ent_w, self.ent_h, self.ent_top, self.ent_bottom, self.ent_left, self.ent_right,
            self.combo_split,
            self.ent_deg, self.btn_rot_apply, self.btn_rot_l, self.btn_rot_r, self.btn_rot_180,
            self.btn_flip_h, self.btn_flip_v,
            self.ent_pad_top, self.ent_pad_bottom, self.ent_pad_left, self.ent_pad_right,
            self.combo_bg, self.btn_pick_bg, self.btn_expand, self.btn_trim_alpha,

            # 分片拉伸
            self.combo_pw_dir, self.combo_pw_unit, self.chk_pw_link, self.ent_pw_x1, self.ent_pw_x2, self.ent_pw_y1, self.ent_pw_y2,
            self.btn_piecewise_preview, self.btn_piecewise_clear_preview, self.btn_piecewise,

            # 按尺寸生成裁剪框
            self.ent_crop_w, self.ent_crop_h, self.btn_crop_by_size,

            # 调色
            self.scale_bri, self.btn_apply_bri, self.btn_reset_bri,
            self.scale_white, self.scale_black, self.btn_apply_white, self.btn_apply_black
        ]:
            try:
                w.configure(state=st)
            except Exception:
                pass

        # 如果浮窗已创建，把浮窗里的控件也同步禁用/启用
        if self.ratio_win and self.ratio_win.winfo_exists():
            for w in [getattr(self, "combo_aspect", None),
                      getattr(self, "ent_aspect_w", None),
                      getattr(self, "ent_aspect_h", None),
                      getattr(self, "combo_crop_ratio_view", None)]:
                try:
                    if w:
                        w.configure(state=st if w != self.combo_aspect else "readonly" if enabled else "disabled")
                except Exception:
                    pass

    # =========================
    # Rotate-chain helpers
    # =========================
    def _reset_rotate_chain(self):
        self._rot_chain_base = None
        self._rot_chain_total_deg = 0.0
        self._last_op = None

    def _mark_op(self, name: str):
        # 非旋转操作会终止“旋转链”，避免逻辑混乱
        if name != "rotate":
            self._reset_rotate_chain()
        self._last_op = name

    # =========================
    # 文件命名辅助（用于分割输出）
    # =========================
    def _safe_stem(self, s: str) -> str:
        s = (s or "").strip() or "image"
        return "".join(ch if (ch.isalnum() or ch in ("-", "_")) else "_" for ch in s)

    def _base_stem(self) -> str:
        if getattr(self, "file_path", None):
            return self._safe_stem(os.path.splitext(os.path.basename(self.file_path))[0])
        return "image"

    # =========================
    # Aspect Ratio
    # =========================
    def _on_aspect_mode(self, event=None):
        if self.aspect_mode.get() == "自定义":
            self.aspect_custom_frame.pack(fill=tk.X, padx=12, pady=(0, 10))
            if not self.ent_aspect_w.get().strip():
                self.ent_aspect_w.insert(0, "1")
            if not self.ent_aspect_h.get().strip():
                self.ent_aspect_h.insert(0, "1")
        else:
            self.aspect_custom_frame.pack_forget()

        if self.image and self.crop_box:
            ratio = self._get_selected_ratio()
            if ratio is not None:
                self.crop_box = self._fit_box_to_ratio_keep_center(self.crop_box, ratio)
                self._update_crop_overlay()

        self._return_focus_to_canvas()

    def _get_selected_ratio(self):
        m = getattr(self, "aspect_mode", tk.StringVar(value="自由")).get()
        preset = {
            "1:1": (1, 1),
            "16:9": (16, 9),
            "9:16": (9, 16),
            "4:3": (4, 3),
            "3:4": (3, 4),
            "3:2": (3, 2),
            "2:3": (2, 3),
        }
        if m == "自由":
            return None
        if m in preset:
            a, b = preset[m]
            return a / b
        if m == "自定义":
            try:
                a = float(self.ent_aspect_w.get())
                b = float(self.ent_aspect_h.get())
                if a > 0 and b > 0:
                    return a / b
            except Exception:
                return None
        return None

    def _active_ratio_for_drag(self, is_new=False):
        sel = self._get_selected_ratio()
        if sel is not None:
            return sel

        if self.shift_down:
            if is_new:
                return 1.0
            if self.crop_box:
                x1, y1, x2, y2 = self.crop_box
                w = max(1, x2 - x1)
                h = max(1, y2 - y1)
                return w / h
        return None

    def _fit_box_to_ratio_keep_center(self, box, ratio: float):
        if not self.image:
            return box
        x1, y1, x2, y2 = box
        cx = (x1 + x2) / 2
        cy = (y1 + y2) / 2
        w = max(1, x2 - x1)
        h = max(1, y2 - y1)

        cur = w / h
        if cur > ratio:
            w2 = h * ratio
            h2 = h
        else:
            w2 = w
            h2 = w / ratio

        nx1 = cx - w2 / 2
        nx2 = cx + w2 / 2
        ny1 = cy - h2 / 2
        ny2 = cy + h2 / 2
        return self._clamp_box((nx1, ny1, nx2, ny2))

    # =========================
    # 坐标 / 绘制
    # =========================
    def _canvas_xy(self, event):
        return self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)

    def _canvas_to_image(self, cx, cy):
        if not self.image:
            return 0, 0
        ix = int(round(cx / self.scale))
        iy = int(round(cy / self.scale))
        return ix, iy

    def _image_to_canvas(self, ix, iy):
        return ix * self.scale, iy * self.scale

    def _clamp_box(self, box):
        if not self.image:
            return None
        x1, y1, x2, y2 = box
        w, h = self.image.size

        x1, x2 = sorted((x1, x2))
        y1, y2 = sorted((y1, y2))

        x1 = max(0, min(x1, w))
        x2 = max(0, min(x2, w))
        y1 = max(0, min(y1, h))
        y2 = max(0, min(y2, h))

        if x2 - x1 < self.MIN_CROP_SIZE:
            x2 = min(w, x1 + self.MIN_CROP_SIZE)
            x1 = max(0, x2 - self.MIN_CROP_SIZE)
        if y2 - y1 < self.MIN_CROP_SIZE:
            y2 = min(h, y1 + self.MIN_CROP_SIZE)
            y1 = max(0, y2 - self.MIN_CROP_SIZE)

        x1 = max(0, min(x1, w - 1))
        y1 = max(0, min(y1, h - 1))
        x2 = max(x1 + 1, min(x2, w))
        y2 = max(y1 + 1, min(y2, h))
        return int(round(x1)), int(round(y1)), int(round(x2)), int(round(y2))

    def _parse_edge_value(self, s: str, max_size: int) -> int:
        s = (s or "").strip()
        if not s:
            return 0
        try:
            if s.endswith("%"):
                v = float(s[:-1]) / 100.0
                px = int(round(max_size * v))
            else:
                px = int(round(float(s)))
            return max(0, min(px, max_size))
        except Exception:
            return 0

    def _make_checkerboard(self, w, h):
        if self._checker_cache_size == (w, h) and self._checker_cache_img is not None:
            return self._checker_cache_img

        cell = self.CHECKER_CELL
        c1 = (235, 235, 235, 255)
        c2 = (200, 200, 200, 255)

        tile = Image.new("RGBA", (cell * 2, cell * 2), c1)
        tile.paste(Image.new("RGBA", (cell, cell), c2), (cell, 0))
        tile.paste(Image.new("RGBA", (cell, cell), c2), (0, cell))

        img = Image.new("RGBA", (w, h), c1)
        for y in range(0, h, cell * 2):
            for x in range(0, w, cell * 2):
                img.paste(tile, (x, y))

        self._checker_cache_size = (w, h)
        self._checker_cache_img = img
        return img

    def _render_to_canvas(self, keep_view_point=None):
        if not self.image:
            self.canvas.delete("all")
            self.tk_img = None
            self.canvas_img_id = None
            self._update_status()
            self._update_crop_analysis()
            return

        iw, ih = self.image.size
        w = max(1, int(round(iw * self.scale)))
        h = max(1, int(round(ih * self.scale)))

        src = self.image
        if src.mode not in ("RGBA", "RGB"):
            src = src.convert("RGBA")

        if src.mode == "RGBA":
            scaled = src.resize((w, h), Image.Resampling.LANCZOS)
            checker = self._make_checkerboard(w, h)
            combined = Image.alpha_composite(checker, scaled)
        else:
            combined = src.resize((w, h), Image.Resampling.LANCZOS)

        self.tk_img = ImageTk.PhotoImage(combined)

        if self.canvas_img_id is None:
            self.canvas_img_id = self.canvas.create_image(0, 0, anchor="nw", image=self.tk_img, tags=("img",))
        else:
            self.canvas.itemconfigure(self.canvas_img_id, image=self.tk_img)

        self.canvas.config(scrollregion=(0, 0, w, h))

        if keep_view_point is not None:
            ix, iy, sx, sy = keep_view_point
            new_cx, new_cy = self._image_to_canvas(ix, iy)
            canvas_w = max(1, self.canvas.winfo_width())
            canvas_h = max(1, self.canvas.winfo_height())

            left = new_cx - sx
            top = new_cy - sy
            left = max(0, min(left, w - canvas_w))
            top = max(0, min(top, h - canvas_h))

            self.canvas.xview_moveto(left / max(1, w))
            self.canvas.yview_moveto(top / max(1, h))

        self._update_crop_overlay()
        self._redraw_piecewise_guides()
        self._update_status()
        self._update_crop_analysis()

    def _update_status(self):
        if not self.image:
            self.lbl_status.config(text="未打开图片")
            self.lbl_zoom.config(text="缩放：100%")
            return

        w, h = self.image.size
        z = int(round(self.scale * 100))
        self.lbl_zoom.config(text=f"缩放：{z}%")

        msg = f"尺寸：{w}×{h}"
        if self.file_path:
            msg = f"{os.path.basename(self.file_path)}  |  " + msg

        if self.crop_box:
            x1, y1, x2, y2 = self.crop_box
            msg += f"  |  裁剪框：({x1},{y1})-({x2},{y2})  {x2-x1}×{y2-y1}"

        self.lbl_status.config(text=msg)

    # =========================
    # 裁剪分析
    # =========================
    def _is_power_of_two(self, n: int) -> bool:
        return n > 0 and (n & (n - 1)) == 0

    def _best_common_ratio(self, w: int, h: int):
        if h <= 0 or w <= 0:
            return None
        r = w / h
        best = None
        for a, b in self.COMMON_RATIOS:
            if a <= 0 or b <= 0:
                continue
            rr = a / b
            err = abs(r - rr)
            if best is None or err < best[2] - 1e-12 or (abs(err - best[2]) < 1e-12 and (a + b) < (best[0] + best[1])):
                best = (a, b, err)
        return best

    def _update_crop_analysis(self):
        if not self.image or not self.crop_box:
            # 如果浮窗还没创建，变量可能还没初始化
            if not hasattr(self, "var_an_size"):
                return

            self.var_an_size.set("当前裁剪：-")
            self.var_an_reduce.set("已约分：-")
            self.var_an_near.set("")
            self.var_an_perfect.set("")
            self.var_an_k.set("")
            self.var_an_decimal.set("")
            self.var_an_multi.set("2/4 倍数：-")
            self.var_an_pow2.set("2 的次幂：-")

            if self.crop_ratio_view_mode.get() == "小数(小边=1)":
                if hasattr(self, "lbl_an_near") and self.lbl_an_near.winfo_ismapped():
                    self.lbl_an_near.pack_forget()
                if hasattr(self, "lbl_an_perfect") and self.lbl_an_perfect.winfo_ismapped():
                    self.lbl_an_perfect.pack_forget()
                if hasattr(self, "lbl_an_k") and self.lbl_an_k.winfo_ismapped():
                    self.lbl_an_k.pack_forget()
                if hasattr(self, "lbl_an_decimal") and (not self.lbl_an_decimal.winfo_ismapped()):
                    self.lbl_an_decimal.pack(anchor=tk.W, padx=8, pady=(0, 2))
            else:
                if hasattr(self, "lbl_an_decimal") and self.lbl_an_decimal.winfo_ismapped():
                    self.lbl_an_decimal.pack_forget()
                if hasattr(self, "lbl_an_near") and (not self.lbl_an_near.winfo_ismapped()):
                    self.lbl_an_near.pack(anchor=tk.W, padx=8, pady=(0, 2))
                if hasattr(self, "lbl_an_perfect") and (not self.lbl_an_perfect.winfo_ismapped()):
                    self.lbl_an_perfect.pack(anchor=tk.W, padx=8, pady=(0, 2))
                if hasattr(self, "lbl_an_k") and (not self.lbl_an_k.winfo_ismapped()):
                    self.lbl_an_k.pack(anchor=tk.W, padx=8, pady=(0, 2))
            return

        if not hasattr(self, "var_an_size"):
            return

        x1, y1, x2, y2 = self.crop_box
        w = max(1, x2 - x1)
        h = max(1, y2 - y1)

        self.var_an_size.set(f"当前裁剪：{w}×{h}")

        g = math.gcd(int(w), int(h))
        rw = int(w) // g
        rh = int(h) // g
        self.var_an_reduce.set(f"已约分：{rw}:{rh}（gcd={g}）")

        w2 = (w % 2 == 0)
        h2 = (h % 2 == 0)
        w4 = (w % 4 == 0)
        h4 = (h % 4 == 0)
        self.var_an_multi.set(
            f"2/4 倍数：2倍(宽={'是' if w2 else '否'}，高={'是' if h2 else '否'})  |  "
            f"4倍(宽={'是' if w4 else '否'}，高={'是' if h4 else '否'})"
        )

        self.var_an_pow2.set(
            f"2 的次幂：宽={'是' if self._is_power_of_two(w) else '否'}  |  高={'是' if self._is_power_of_two(h) else '否'}"
        )

        mode = self.crop_ratio_view_mode.get()

        if mode == "小数(小边=1)":
            small = min(w, h)
            big = max(w, h)
            if small <= 0:
                ratio_s = "-"
            else:
                k = big / small
                ratio_s = f"{k:.3f}:1" if w >= h else f"1:{k:.3f}"
            self.var_an_decimal.set(f"小数比例(小边=1)：{ratio_s}")

            if self.lbl_an_near.winfo_ismapped():
                self.lbl_an_near.pack_forget()
            if self.lbl_an_perfect.winfo_ismapped():
                self.lbl_an_perfect.pack_forget()
            if self.lbl_an_k.winfo_ismapped():
                self.lbl_an_k.pack_forget()
            if not self.lbl_an_decimal.winfo_ismapped():
                self.lbl_an_decimal.pack(anchor=tk.W, padx=8, pady=(0, 2))
            return

        best = self._best_common_ratio(w, h)
        if not best:
            self.var_an_near.set("最接近比例：-")
            self.var_an_perfect.set("最接近完美比例尺寸：-")
            self.var_an_k.set("约分与比例倍率：-")
        else:
            a, b, _err = best
            gg = math.gcd(a, b)
            aa, bb = a // gg, b // gg
            self.var_an_near.set(f"最接近比例：{aa}:{bb}（已约分）")

            kk = int(round((w / a + h / b) / 2.0))
            kk = max(1, kk)
            pw = a * kk
            ph = b * kk
            dw = pw - w
            dh = ph - h
            self.var_an_perfect.set(f"最接近完美比例尺寸：{pw}:{ph}（ΔW={dw:+d}, ΔH={dh:+d}）")
            self.var_an_k.set(f"约分与比例倍率：{kk}")

        if self.lbl_an_decimal.winfo_ismapped():
            self.lbl_an_decimal.pack_forget()
        if not self.lbl_an_near.winfo_ismapped():
            self.lbl_an_near.pack(anchor=tk.W, padx=8, pady=(0, 2))
        if not self.lbl_an_perfect.winfo_ismapped():
            self.lbl_an_perfect.pack(anchor=tk.W, padx=8, pady=(0, 2))
        if not self.lbl_an_k.winfo_ismapped():
            self.lbl_an_k.pack(anchor=tk.W, padx=8, pady=(0, 2))

    # =========================
    # 打开 / 保存 / Undo / Redo
    # =========================
    def open_image(self):
        path = filedialog.askopenfilename(
            title="选择图片",
            filetypes=[("图片文件", "*.png *.jpg *.jpeg *.bmp *.gif"), ("所有文件", "*.*")]
        )
        if not path:
            return
        try:
            img = Image.open(path)
            if img.mode not in ("RGBA", "RGB"):
                img = img.convert("RGBA")
            self.image = img
            self.file_path = path

            self.undo_stack.clear()
            self.redo_stack.clear()

            self.scale = 1.0
            self.crop_box = None
            self._destroy_crop_items()

            # 清掉分片预览线（避免旧图残留）
            self.clear_piecewise_guides()

            self.ent_w.delete(0, tk.END)
            self.ent_h.delete(0, tk.END)
            self.ent_w.insert(0, str(img.size[0]))
            self.ent_h.insert(0, str(img.size[1]))

            # 按尺寸生成裁剪框：默认给当前尺寸（方便直接改）
            try:
                self.ent_crop_w.delete(0, tk.END)
                self.ent_crop_h.delete(0, tk.END)
                self.ent_crop_w.insert(0, str(img.size[0]))
                self.ent_crop_h.insert(0, str(img.size[1]))
            except Exception:
                pass

            self._checker_cache_size = None
            self._checker_cache_img = None

            self._reset_rotate_chain()
            self._set_ui_enabled(True)
            self._refresh_undo_redo_state()
            self._render_to_canvas()

            # 打开图片后，如果浮窗开着，刷新并浮上
            if self._ratio_win_visible:
                self._update_crop_analysis()
                self._lift_ratio_window()

        except Exception as e:
            messagebox.showerror("错误", f"打开失败：{e}")

    def save_image(self):
        if not self.image:
            return
        path = filedialog.asksaveasfilename(
            title="保存图片",
            defaultextension=".png",
            filetypes=[("PNG（保留透明）", "*.png"),
                       ("JPG", "*.jpg *.jpeg"),
                       ("BMP", "*.bmp"),
                       ("所有文件", "*.*")]
        )
        if not path:
            return
        try:
            img = self.image
            ext = os.path.splitext(path)[1].lower()
            if ext in (".jpg", ".jpeg"):
                if img.mode == "RGBA":
                    img = img.convert("RGB")
                img.save(path, quality=95, optimize=True)
            else:
                img.save(path, optimize=True)
            messagebox.showinfo("完成", "保存成功")
        except Exception as e:
            messagebox.showerror("错误", f"保存失败：{e}")
        self._return_focus_to_canvas()

    def _push_undo(self):
        if self.image:
            self.undo_stack.append(self.image.copy())
            self.redo_stack.clear()
        self._refresh_undo_redo_state()

    def _refresh_undo_redo_state(self):
        self.btn_undo.configure(state=("normal" if self.undo_stack else "disabled"))
        self.btn_redo.configure(state=("normal" if self.redo_stack else "disabled"))

    def undo(self):
        if not self.undo_stack or not self.image:
            return
        self.redo_stack.append(self.image.copy())
        self.image = self.undo_stack.pop()
        self._after_image_changed(op_name="other")
        self._return_focus_to_canvas()

    def redo(self):
        if not self.redo_stack or not self.image:
            return
        self.undo_stack.append(self.image.copy())
        self.image = self.redo_stack.pop()
        self._after_image_changed(op_name="other")
        self._return_focus_to_canvas()

    def _after_image_changed(self, op_name="other", keep_center=False):
        self._mark_op(op_name)

        self.crop_box = None
        self._destroy_crop_items()
        self._checker_cache_size = None
        self._checker_cache_img = None

        self.clear_piecewise_guides()

        self.ent_w.delete(0, tk.END)
        self.ent_h.delete(0, tk.END)
        self.ent_w.insert(0, str(self.image.size[0]))
        self.ent_h.insert(0, str(self.image.size[1]))

        self._refresh_undo_redo_state()

        if keep_center:
            cw = max(1, self.canvas.winfo_width())
            ch = max(1, self.canvas.winfo_height())
            sx, sy = cw / 2, ch / 2
            nw, nh = self.image.size
            self._render_to_canvas(keep_view_point=(nw / 2, nh / 2, sx, sy))
        else:
            self._render_to_canvas()

        self._return_focus_to_canvas()

    # =========================
    # Zoom / Pan
    # =========================
    def zoom_100(self):
        if not self.image:
            return
        self.scale = 1.0
        self._checker_cache_size = None
        self._checker_cache_img = None
        self._render_to_canvas()
        self._return_focus_to_canvas()

    def fit_to_view(self):
        if not self.image:
            return
        iw, ih = self.image.size
        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        margin = 20
        sx = (cw - margin) / iw
        sy = (ch - margin) / ih
        self.scale = max(self.ZOOM_MIN, min(self.ZOOM_MAX, min(sx, sy)))
        self._checker_cache_size = None
        self._checker_cache_img = None
        self._render_to_canvas()
        self._return_focus_to_canvas()

    def _on_wheel(self, event):
        if not self.image:
            return
        cx, cy = self._canvas_xy(event)
        ix, iy = self._canvas_to_image(cx, cy)

        factor = 1.1 if event.delta > 0 else 0.9
        new_scale = self.scale * factor
        new_scale = max(self.ZOOM_MIN, min(self.ZOOM_MAX, new_scale))
        if abs(new_scale - self.scale) < 1e-6:
            return
        self.scale = new_scale
        self._checker_cache_size = None
        self._checker_cache_img = None
        self._render_to_canvas(keep_view_point=(ix, iy, event.x, event.y))

    def _on_wheel_linux(self, event):
        if not self.image:
            return
        cx, cy = self._canvas_xy(event)
        ix, iy = self._canvas_to_image(cx, cy)

        factor = 1.1 if event.num == 4 else 0.9
        new_scale = self.scale * factor
        new_scale = max(self.ZOOM_MIN, min(self.ZOOM_MAX, new_scale))
        if abs(new_scale - self.scale) < 1e-6:
            return
        self.scale = new_scale
        self._checker_cache_size = None
        self._checker_cache_img = None
        self._render_to_canvas(keep_view_point=(ix, iy, event.x, event.y))

    def _on_pan_start(self, event):
        if not self.image:
            return
        self.canvas.focus_set()
        self.canvas.scan_mark(event.x, event.y)

    def _on_pan_drag(self, event):
        if not self.image:
            return
        self.canvas.scan_dragto(event.x, event.y, gain=1)

    # =========================
    # Crop Overlay
    # =========================
    def _destroy_crop_items(self):
        for i in self.shade_ids:
            try:
                self.canvas.delete(i)
            except Exception:
                pass
        self.shade_ids = []
        for _, i in list(self.handle_ids.items()):
            try:
                self.canvas.delete(i)
            except Exception:
                pass
        self.handle_ids = {}
        if self.crop_rect_id is not None:
            try:
                self.canvas.delete(self.crop_rect_id)
            except Exception:
                pass
        self.crop_rect_id = None

    def _ensure_crop_items(self):
        if not self.image:
            return
        if not self.shade_ids:
            for _ in range(4):
                rid = self.canvas.create_rectangle(0, 0, 0, 0, fill="#000000",
                                                   stipple="gray25", outline="", tags=("shade",))
                self.shade_ids.append(rid)

        if self.crop_rect_id is None:
            self.crop_rect_id = self.canvas.create_rectangle(
                0, 0, 0, 0,
                outline=self.ACCENT, width=2, dash=(6, 4),
                tags=("crop_rect",)
            )

        if not self.handle_ids:
            for pos in ("nw", "n", "ne", "w", "e", "sw", "s", "se"):
                hid = self.canvas.create_rectangle(
                    0, 0, 0, 0,
                    fill="white", outline=self.ACCENT, width=2,
                    tags=("handle", f"h_{pos}")
                )
                self.handle_ids[pos] = hid

        self.canvas.tag_raise("shade")
        self.canvas.tag_raise("crop_rect")
        self.canvas.tag_raise("handle")

    def _update_crop_overlay(self):
        if not self.image or not self.crop_box:
            self._destroy_crop_items()
            self._update_status()
            self._update_crop_analysis()
            return

        self._ensure_crop_items()

        iw, ih = self.image.size
        x1, y1, x2, y2 = self.crop_box

        cx1, cy1 = self._image_to_canvas(x1, y1)
        cx2, cy2 = self._image_to_canvas(x2, y2)
        w = int(round(iw * self.scale))
        h = int(round(ih * self.scale))

        self.canvas.coords(self.crop_rect_id, cx1, cy1, cx2, cy2)

        self.canvas.coords(self.shade_ids[0], 0, 0, w, cy1)
        self.canvas.coords(self.shade_ids[1], 0, cy2, w, h)
        self.canvas.coords(self.shade_ids[2], 0, cy1, cx1, cy2)
        self.canvas.coords(self.shade_ids[3], cx2, cy1, w, cy2)

        hs = self.HANDLE_SIZE
        mx = (cx1 + cx2) / 2
        my = (cy1 + cy2) / 2

        def set_handle(pos, x, y):
            self.canvas.coords(self.handle_ids[pos], x - hs, y - hs, x + hs, y + hs)

        set_handle("nw", cx1, cy1)
        set_handle("n", mx, cy1)
        set_handle("ne", cx2, cy1)
        set_handle("w", cx1, my)
        set_handle("e", cx2, my)
        set_handle("sw", cx1, cy2)
        set_handle("s", mx, cy2)
        set_handle("se", cx2, cy2)

        self._update_status()
        self._update_crop_analysis()

    def clear_crop(self):
        self.crop_box = None
        self._destroy_crop_items()
        self._update_status()
        self._update_crop_analysis()
        self._return_focus_to_canvas()

    def _hit_test(self, event):
        if not self.crop_box:
            return None, None
        item = self.canvas.find_withtag("current")
        if not item:
            return None, None
        tags = set(self.canvas.gettags(item[0]))
        if "handle" in tags:
            for t in tags:
                if t.startswith("h_"):
                    return "handle", t[2:]
        if "crop_rect" in tags:
            return "rect", None
        return None, None

    def _on_mouse_move(self, event):
        if not self.image:
            self.canvas.config(cursor="arrow")
            return
        kind, pos = self._hit_test(event)
        cursor = "arrow"
        if kind == "handle":
            cursor_map = {
                "nw": "size_nw_se", "se": "size_nw_se",
                "ne": "size_ne_sw", "sw": "size_ne_sw",
                "n": "sb_v_double_arrow", "s": "sb_v_double_arrow",
                "w": "sb_h_double_arrow", "e": "sb_h_double_arrow",
            }
            cursor = cursor_map.get(pos, "arrow")
        elif kind == "rect":
            cursor = "fleur"
        else:
            cursor = "crosshair"
        self.canvas.config(cursor=cursor)

    # =========================
    # “专业手感”比例：边拖动中心对称
    # =========================
    def _side_center_symmetric_box(self, cx, cy, handle, ix, iy, ratio):
        iw, ih = self.image.size

        max_half_w = min(cx, iw - cx)
        max_half_h = min(cy, ih - cy)

        if handle in ("e", "w"):
            half_w = abs(ix - cx)

            w_min = max(self.MIN_CROP_SIZE, self.MIN_CROP_SIZE * ratio)
            half_w = max(half_w, w_min / 2)

            half_w = min(half_w, max_half_w, max_half_h * ratio)
            half_h = half_w / ratio

        else:  # "n","s"
            half_h = abs(iy - cy)

            h_min = max(self.MIN_CROP_SIZE, self.MIN_CROP_SIZE / ratio)
            half_h = max(half_h, h_min / 2)

            half_h = min(half_h, max_half_h, max_half_w / ratio)
            half_w = half_h * ratio

        x1 = cx - half_w
        x2 = cx + half_w
        y1 = cy - half_h
        y2 = cy + half_h
        return self._clamp_box((x1, y1, x2, y2))

    def _apply_ratio_resize_corner(self, box, handle, ratio):
        x1, y1, x2, y2 = box
        iw, ih = self.image.size

        if handle == "nw":
            fx, fy = x2, y2
            w = max(1, fx - x1)
            h2 = int(round(w / ratio))
            w2 = min(w, fx)
            h2 = min(h2, fy)
            w2 = min(w2, int(round(h2 * ratio)))
            h2 = int(round(w2 / ratio))
            return self._clamp_box((fx - w2, fy - h2, fx, fy))

        if handle == "ne":
            fx, fy = x1, y2
            w = max(1, x2 - fx)
            h2 = int(round(w / ratio))
            w2 = min(w, iw - fx)
            h2 = min(h2, fy)
            w2 = min(w2, int(round(h2 * ratio)))
            h2 = int(round(w2 / ratio))
            return self._clamp_box((fx, fy - h2, fx + w2, fy))

        if handle == "sw":
            fx, fy = x2, y1
            w = max(1, fx - x1)
            h2 = int(round(w / ratio))
            w2 = min(w, fx)
            h2 = min(h2, ih - fy)
            w2 = min(w2, int(round(h2 * ratio)))
            h2 = int(round(w2 / ratio))
            return self._clamp_box((fx - w2, fy, fx, fy + h2))

        if handle == "se":
            fx, fy = x1, y1
            w = max(1, x2 - fx)
            h2 = int(round(w / ratio))
            w2 = min(w, iw - fx)
            h2 = min(h2, ih - fy)
            w2 = min(w2, int(round(h2 * ratio)))
            h2 = int(round(w2 / ratio))
            return self._clamp_box((fx, fy, fx + w2, fy + h2))

        return self._clamp_box(box)

    # =========================
    # Space 临时移动裁剪框（保持尺寸）
    # =========================
    def _move_crop_by(self, dx, dy):
        if not self.image or not self.crop_box:
            return
        x1, y1, x2, y2 = self.crop_box
        iw, ih = self.image.size
        bw = x2 - x1
        bh = y2 - y1

        nx1 = max(0, min(x1 + dx, iw - bw))
        ny1 = max(0, min(y1 + dy, ih - bh))
        self.crop_box = (int(nx1), int(ny1), int(nx1 + bw), int(ny1 + bh))

    # =========================
    # Crop Drag
    # =========================
    def _on_lmb_down(self, event):
        if not self.image:
            return

        self.canvas.focus_set()

        cx, cy = self._canvas_xy(event)
        ix, iy = self._canvas_to_image(cx, cy)

        kind, pos = self._hit_test(event)

        if kind == "handle":
            self._drag_mode = "resize"
            self._drag_handle = pos
            self._drag_anchor = (ix, iy)
            self._drag_last = (ix, iy)
            if self.crop_box:
                x1, y1, x2, y2 = self.crop_box
                self._resize_base_center = ((x1 + x2) / 2, (y1 + y2) / 2)
                self._resize_base_box = self.crop_box
            return

        if kind == "rect":
            self._drag_mode = "move"
            self._drag_anchor = (ix, iy)
            self._drag_last = (ix, iy)
            return

        self._drag_mode = "new"
        self._drag_anchor = (ix, iy)
        self._drag_last = (ix, iy)
        self.crop_box = self._clamp_box((ix, iy, ix + self.MIN_CROP_SIZE, iy + self.MIN_CROP_SIZE))
        self._update_crop_overlay()

    def _apply_ratio_new(self, ax, ay, ix, iy, ratio: float):
        dx = ix - ax
        dy = iy - ay
        if dx == 0 and dy == 0:
            return ix, iy
        sx = 1 if dx >= 0 else -1
        sy = 1 if dy >= 0 else -1
        adx = abs(dx)
        ady = abs(dy)

        if ady == 0:
            ady = max(1, int(round(adx / ratio)))
        else:
            cur = adx / ady if ady != 0 else ratio
            if cur > ratio:
                adx = int(round(ady * ratio))
            else:
                ady = int(round(adx / ratio))

        return ax + sx * adx, ay + sy * ady

    def _on_lmb_drag(self, event):
        if not self.image or not self._drag_mode:
            return
        cx, cy = self._canvas_xy(event)
        ix, iy = self._canvas_to_image(cx, cy)
        iw, ih = self.image.size
        ix = max(0, min(ix, iw))
        iy = max(0, min(iy, ih))

        if self.space_down and self._drag_mode in ("move", "resize") and self.crop_box and self._drag_last:
            lx, ly = self._drag_last
            dx = ix - lx
            dy = iy - ly
            self._move_crop_by(dx, dy)
            self._update_crop_overlay()
            self._drag_last = (ix, iy)
            return

        if self._drag_mode == "new":
            ax, ay = self._drag_anchor
            ratio = self._active_ratio_for_drag(is_new=True)
            if ratio is not None:
                ix, iy = self._apply_ratio_new(ax, ay, ix, iy, ratio)
            self.crop_box = self._clamp_box((ax, ay, ix, iy))
            self._update_crop_overlay()
            self._drag_last = (ix, iy)
            return

        if not self.crop_box:
            return

        x1, y1, x2, y2 = self.crop_box

        if self._drag_mode == "move":
            lx, ly = self._drag_last
            dx = ix - lx
            dy = iy - ly
            nx1, ny1, nx2, ny2 = x1 + dx, y1 + dy, x2 + dx, y2 + dy

            bw = nx2 - nx1
            bh = ny2 - ny1
            nx1 = max(0, min(nx1, iw - bw))
            ny1 = max(0, min(ny1, ih - bh))
            nx2 = nx1 + bw
            ny2 = ny1 + bh

            self.crop_box = (int(nx1), int(ny1), int(nx2), int(ny2))
            self._update_crop_overlay()
            self._drag_last = (ix, iy)
            return

        if self._drag_mode == "resize":
            hnd = self._drag_handle
            ratio = self._active_ratio_for_drag(is_new=False)

            if ratio is not None and hnd in ("n", "s", "e", "w") and self._resize_base_center:
                rcx, rcy = self._resize_base_center
                self.crop_box = self._side_center_symmetric_box(rcx, rcy, hnd, ix, iy, ratio)
                self._update_crop_overlay()
                self._drag_last = (ix, iy)
                return

            if hnd == "nw":
                x1, y1 = ix, iy
            elif hnd == "n":
                y1 = iy
            elif hnd == "ne":
                x2, y1 = ix, iy
            elif hnd == "w":
                x1 = ix
            elif hnd == "e":
                x2 = ix
            elif hnd == "sw":
                x1, y2 = ix, iy
            elif hnd == "s":
                y2 = iy
            elif hnd == "se":
                x2, y2 = ix, iy

            box = self._clamp_box((x1, y1, x2, y2))
            if ratio is not None and hnd in ("nw", "ne", "sw", "se"):
                box = self._apply_ratio_resize_corner(box, hnd, ratio)

            self.crop_box = box
            self._update_crop_overlay()
            self._drag_last = (ix, iy)
            return

    def _on_lmb_up(self, event):
        self._drag_mode = None
        self._drag_handle = None
        self._drag_anchor = None
        self._drag_last = None
        self._resize_base_center = None
        self._resize_base_box = None

    # =========================
    # 键盘微调
    # =========================
    def _focus_is_text_input(self):
        w = self.root.focus_get()
        return isinstance(w, (tk.Entry, ttk.Entry, ttk.Combobox))

    def _on_arrow(self, key: str):
        if not self.image or not self.crop_box:
            return
        if self._focus_is_text_input():
            return

        step = 10 if self.shift_down else 1
        x1, y1, x2, y2 = self.crop_box
        iw, ih = self.image.size

        ratio_sel = self._get_selected_ratio()
        if ratio_sel is None and self.shift_down:
            w = max(1, x2 - x1)
            h = max(1, y2 - y1)
            ratio_sel = w / h

        cx = (x1 + x2) / 2
        cy = (y1 + y2) / 2

        if self.ctrl_down:
            shrink = self.shift_down
            d = step

            if key == "Left":
                new_edge = (x1 + d) if shrink else (x1 - d)
                handle = "w"
            elif key == "Right":
                new_edge = (x2 - d) if shrink else (x2 + d)
                handle = "e"
            elif key == "Up":
                new_edge = (y1 + d) if shrink else (y1 - d)
                handle = "n"
            else:
                new_edge = (y2 - d) if shrink else (y2 + d)
                handle = "s"

            if ratio_sel is not None and handle in ("n", "s", "e", "w"):
                if handle in ("e", "w"):
                    self.crop_box = self._side_center_symmetric_box(cx, cy, handle, new_edge, cy, ratio_sel)
                else:
                    self.crop_box = self._side_center_symmetric_box(cx, cy, handle, cx, new_edge, ratio_sel)
            else:
                if handle == "w":
                    x1 = new_edge
                elif handle == "e":
                    x2 = new_edge
                elif handle == "n":
                    y1 = new_edge
                else:
                    y2 = new_edge
                self.crop_box = self._clamp_box((x1, y1, x2, y2))

            self._update_crop_overlay()
            return

        dx = dy = 0
        if key == "Left":
            dx = -step
        elif key == "Right":
            dx = step
        elif key == "Up":
            dy = -step
        else:
            dy = step

        bw = x2 - x1
        bh = y2 - y1
        nx1 = max(0, min(x1 + dx, iw - bw))
        ny1 = max(0, min(y1 + dy, ih - bh))
        nx2 = nx1 + bw
        ny2 = ny1 + bh

        self.crop_box = (int(nx1), int(ny1), int(nx2), int(ny2))
        self._update_crop_overlay()

    # =========================
    # 裁剪：边缘参数 & 应用
    # =========================
    def edge_crop_preview(self):
        if not self.image:
            return
        iw, ih = self.image.size
        top = self._parse_edge_value(self.ent_top.get(), ih)
        bottom = self._parse_edge_value(self.ent_bottom.get(), ih)
        left = self._parse_edge_value(self.ent_left.get(), iw)
        right = self._parse_edge_value(self.ent_right.get(), iw)

        x1 = left
        y1 = top
        x2 = iw - right
        y2 = ih - bottom
        if x2 <= x1 or y2 <= y1:
            messagebox.showerror("错误", "裁剪参数无效：裁剪后尺寸 <= 0")
            return

        self.crop_box = self._clamp_box((x1, y1, x2, y2))

        ratio = self._get_selected_ratio()
        if ratio is not None:
            self.crop_box = self._fit_box_to_ratio_keep_center(self.crop_box, ratio)

        self._update_crop_overlay()
        self._return_focus_to_canvas()

    def crop_box_by_size_preview(self):
        if not self.image:
            return
        iw, ih = self.image.size
        try:
            cw = int(float(self.ent_crop_w.get()))
            ch = int(float(self.ent_crop_h.get()))
        except Exception:
            messagebox.showerror("错误", "请输入有效的宽高数字（px）")
            return

        if cw < self.MIN_CROP_SIZE or ch < self.MIN_CROP_SIZE:
            messagebox.showerror("错误", f"裁剪框宽高不能小于 {self.MIN_CROP_SIZE}px")
            return

        cw = min(cw, iw)
        ch = min(ch, ih)

        x1 = int(round((iw - cw) / 2))
        y1 = int(round((ih - ch) / 2))
        x2 = x1 + cw
        y2 = y1 + ch

        self.crop_box = self._clamp_box((x1, y1, x2, y2))
        self._update_crop_overlay()
        self._return_focus_to_canvas()

    def apply_crop(self):
        if not self.image or not self.crop_box:
            return
        x1, y1, x2, y2 = self.crop_box
        if x2 <= x1 or y2 <= y1:
            return
        self._push_undo()
        self.image = self.image.crop((x1, y1, x2, y2))
        self._after_image_changed(op_name="other")
        self._return_focus_to_canvas()

    # =========================
    # 缩放 / 拉伸 / 组合应用
    # =========================
    def _read_wh(self):
        try:
            w = int(float(self.ent_w.get()))
            h = int(float(self.ent_h.get()))
            if w <= 0 or h <= 0:
                raise ValueError
            return w, h
        except Exception:
            messagebox.showerror("错误", "请输入有效的宽高数字（>0）")
            return None

    def apply_resize(self):
        if not self.image:
            return
        wh = self._read_wh()
        if not wh:
            return
        new_w, new_h = wh
        if self.lock_ratio_resize.get():
            w0, h0 = self.image.size
            ratio = w0 / h0
            new_h = max(1, int(round(new_w / ratio)))
            self.ent_h.delete(0, tk.END)
            self.ent_h.insert(0, str(new_h))

        self._push_undo()
        self.image = self.image.resize((new_w, new_h), Image.Resampling.LANCZOS)
        self._after_image_changed(op_name="other")
        self._return_focus_to_canvas()

    def apply_stretch(self):
        if not self.image:
            return
        wh = self._read_wh()
        if not wh:
            return
        new_w, new_h = wh
        self._push_undo()
        self.image = self.image.resize((new_w, new_h), Image.Resampling.BILINEAR)
        self._after_image_changed(op_name="other")
        self._return_focus_to_canvas()

    def apply_crop_and_resize(self):
        if not self.image:
            return
        wh = self._read_wh()
        if not wh:
            return
        new_w, new_h = wh

        self._push_undo()
        img = self.image

        if self.crop_box:
            x1, y1, x2, y2 = self.crop_box
            img = img.crop((x1, y1, x2, y2))

        if self.lock_ratio_resize.get():
            w0, h0 = img.size
            ratio = w0 / h0
            new_h = max(1, int(round(new_w / ratio)))
            self.ent_h.delete(0, tk.END)
            self.ent_h.insert(0, str(new_h))
            img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
        else:
            img = img.resize((new_w, new_h), Image.Resampling.BILINEAR)

        self.image = img
        self._after_image_changed(op_name="other")
        self._return_focus_to_canvas()

    # =========================
    # 分片拉伸（你原逻辑保留）
    # =========================
    def _on_pw_unit_change(self, event=None):
        u = self.pw_unit.get()
        if u.startswith("像素"):
            self.lbl_pw_x.config(text="横向拉伸区域(px)")
            self.lbl_pw_y.config(text="纵向拉伸区域(px)")
        else:
            self.lbl_pw_x.config(text="横向拉伸区域(%)")
            self.lbl_pw_y.config(text="纵向拉伸区域(%)")

        if self._pw_guides_state is not None:
            self.preview_piecewise_guides()

    def _read_percent(self, s: str, default: float) -> float:
        s = (s or "").strip()
        if not s:
            return default
        try:
            if s.endswith("%"):
                v = float(s[:-1])
            else:
                v = float(s)
            v = max(0.0, min(100.0, v))
            return v / 100.0
        except Exception:
            return default

    def _read_px(self, s: str, default: int, max_size: int) -> int:
        s = (s or "").strip().lower()
        if not s:
            return max(0, min(int(default), int(max_size)))
        try:
            if s.endswith("px"):
                s = s[:-2].strip()
            v = int(round(float(s)))
            return max(0, min(v, int(max_size)))
        except Exception:
            return max(0, min(int(default), int(max_size)))

    def _calc_pw_bounds_px(self):
        if not self.image:
            raise ValueError("未打开图片")
        iw, ih = self.image.size

        u = self.pw_unit.get()
        if u.startswith("像素"):
            xa = self._read_px(self.ent_pw_x1.get(), int(iw * 0.2), iw)
            xb = self._read_px(self.ent_pw_x2.get(), int(iw * 0.8), iw)
            ya = self._read_px(self.ent_pw_y1.get(), int(ih * 0.2), ih)
            yb = self._read_px(self.ent_pw_y2.get(), int(ih * 0.8), ih)
        else:
            x1p = self._read_percent(self.ent_pw_x1.get(), 0.2)
            x2p = self._read_percent(self.ent_pw_x2.get(), 0.8)
            y1p = self._read_percent(self.ent_pw_y1.get(), 0.2)
            y2p = self._read_percent(self.ent_pw_y2.get(), 0.8)
            xa = int(round(iw * x1p))
            xb = int(round(iw * x2p))
            ya = int(round(ih * y1p))
            yb = int(round(ih * y2p))

        xa = max(0, min(xa, iw))
        xb = max(0, min(xb, iw))
        ya = max(0, min(ya, ih))
        yb = max(0, min(yb, ih))

        if xb <= xa:
            raise ValueError("横向拉伸区域无效：起点必须小于终点")
        if yb <= ya:
            raise ValueError("纵向拉伸区域无效：起点必须小于终点")

        return xa, xb, ya, yb

    def clear_piecewise_guides(self):
        for i in list(self._pw_guide_ids):
            try:
                self.canvas.delete(i)
            except Exception:
                pass
        self._pw_guide_ids = []
        self._pw_guides_state = None

    def _redraw_piecewise_guides(self):
        if not self.image or not self._pw_guides_state:
            if self._pw_guide_ids:
                for i in list(self._pw_guide_ids):
                    try:
                        self.canvas.delete(i)
                    except Exception:
                        pass
                self._pw_guide_ids = []
            return

        st = self._pw_guides_state
        mode = st.get("mode")
        xa = int(st.get("xa", 0))
        xb = int(st.get("xb", 0))
        ya = int(st.get("ya", 0))
        yb = int(st.get("yb", 0))

        iw, ih = self.image.size
        xa = max(0, min(xa, iw))
        xb = max(0, min(xb, iw))
        ya = max(0, min(ya, ih))
        yb = max(0, min(yb, ih))

        for i in list(self._pw_guide_ids):
            try:
                self.canvas.delete(i)
            except Exception:
                pass
        self._pw_guide_ids = []

        w_canvas = int(round(iw * self.scale))
        h_canvas = int(round(ih * self.scale))

        def vline(x_img):
            x = self._image_to_canvas(x_img, 0)[0]
            lid = self.canvas.create_line(x, 0, x, h_canvas, fill=self.ACCENT, dash=(6, 4), width=2, tags=("pw_guides",))
            self._pw_guide_ids.append(lid)

        def hline(y_img):
            y = self._image_to_canvas(0, y_img)[1]
            lid = self.canvas.create_line(0, y, w_canvas, y, fill=self.ACCENT, dash=(6, 4), width=2, tags=("pw_guides",))
            self._pw_guide_ids.append(lid)

        if mode.startswith("横向"):
            vline(xa)
            vline(xb)
        elif mode.startswith("纵向"):
            hline(ya)
            hline(yb)
        else:
            vline(xa)
            vline(xb)
            hline(ya)
            hline(yb)

        for i in self._pw_guide_ids:
            try:
                self.canvas.tag_raise(i)
            except Exception:
                pass

    def preview_piecewise_guides(self):
        if not self.image:
            return
        try:
            xa, xb, ya, yb = self._calc_pw_bounds_px()
        except Exception as e:
            messagebox.showerror("错误", f"预览失败：{e}")
            return

        mode = self.pw_dir.get()
        self._pw_guides_state = {"mode": mode, "xa": xa, "xb": xb, "ya": ya, "yb": yb}
        self._redraw_piecewise_guides()
        self._return_focus_to_canvas()

    def _piecewise_resize_h_px(self, img: Image.Image, new_w: int, xa: int, xb: int) -> Image.Image:
        iw, ih = img.size
        xa = max(0, min(int(xa), iw))
        xb = max(0, min(int(xb), iw))

        if xb <= xa:
            raise ValueError("横向拉伸区域无效：起点必须小于终点")

        left_w = xa
        mid_w = xb - xa
        right_w = iw - xb
        new_mid_w = new_w - left_w - right_w
        if new_mid_w < 1:
            raise ValueError("目标宽度太小：小于左右保护边缘之和，无法分片拉伸")

        left = img.crop((0, 0, xa, ih))
        mid = img.crop((xa, 0, xb, ih))
        right = img.crop((xb, 0, iw, ih))

        mid2 = mid.resize((new_mid_w, ih), Image.Resampling.BILINEAR)

        out = Image.new(img.mode, (new_w, ih))
        x = 0
        if left_w > 0:
            out.paste(left, (x, 0))
            x += left_w
        out.paste(mid2, (x, 0))
        x += new_mid_w
        if right_w > 0:
            out.paste(right, (x, 0))
        return out

    def _piecewise_resize_v_px(self, img: Image.Image, new_h: int, ya: int, yb: int) -> Image.Image:
        iw, ih = img.size
        ya = max(0, min(int(ya), ih))
        yb = max(0, min(int(yb), ih))

        if yb <= ya:
            raise ValueError("纵向拉伸区域无效：起点必须小于终点")

        top_h = ya
        mid_h = yb - ya
        bot_h = ih - yb
        new_mid_h = new_h - top_h - bot_h
        if new_mid_h < 1:
            raise ValueError("目标高度太小：小于上下保护边缘之和，无法分片拉伸")

        top = img.crop((0, 0, iw, ya))
        mid = img.crop((0, ya, iw, yb))
        bot = img.crop((0, yb, iw, ih))

        mid2 = mid.resize((iw, new_mid_h), Image.Resampling.BILINEAR)

        out = Image.new(img.mode, (iw, new_h))
        y = 0
        if top_h > 0:
            out.paste(top, (0, y))
            y += top_h
        out.paste(mid2, (0, y))
        y += new_mid_h
        if bot_h > 0:
            out.paste(bot, (0, y))
        return out

    def _nine_slice_resize_px(self, img: Image.Image, new_w: int, new_h: int,
                              xa: int, xb: int, ya: int, yb: int) -> Image.Image:
        iw, ih = img.size
        xa = max(0, min(int(xa), iw))
        xb = max(0, min(int(xb), iw))
        ya = max(0, min(int(ya), ih))
        yb = max(0, min(int(yb), ih))

        if xb <= xa or yb <= ya:
            raise ValueError("双向拉伸区域无效：横纵起点必须小于终点")

        left_w = xa
        right_w = iw - xb
        top_h = ya
        bot_h = ih - yb

        new_mid_w = new_w - left_w - right_w
        new_mid_h = new_h - top_h - bot_h
        if new_mid_w < 1 or new_mid_h < 1:
            raise ValueError("目标尺寸太小：小于边缘保护尺寸之和，无法九宫格拉伸")

        TL = img.crop((0, 0, xa, ya))
        TM = img.crop((xa, 0, xb, ya))
        TR = img.crop((xb, 0, iw, ya))

        ML = img.crop((0, ya, xa, yb))
        MM = img.crop((xa, ya, xb, yb))
        MR = img.crop((xb, ya, iw, yb))

        BL = img.crop((0, yb, xa, ih))
        BM = img.crop((xa, yb, xb, ih))
        BR = img.crop((xb, yb, iw, ih))

        TM2 = TM.resize((new_mid_w, top_h), Image.Resampling.BILINEAR) if top_h > 0 else TM
        BM2 = BM.resize((new_mid_w, bot_h), Image.Resampling.BILINEAR) if bot_h > 0 else BM
        ML2 = ML.resize((left_w, new_mid_h), Image.Resampling.BILINEAR) if left_w > 0 else ML
        MR2 = MR.resize((right_w, new_mid_h), Image.Resampling.BILINEAR) if right_w > 0 else MR
        MM2 = MM.resize((new_mid_w, new_mid_h), Image.Resampling.BILINEAR)

        out = Image.new(img.mode, (new_w, new_h))

        xL = 0
        xM = left_w
        xR = left_w + new_mid_w

        yT = 0
        yM = top_h
        yB = top_h + new_mid_h

        if left_w > 0 and top_h > 0:
            out.paste(TL, (xL, yT))
        if top_h > 0:
            out.paste(TM2, (xM, yT))
        if right_w > 0 and top_h > 0:
            out.paste(TR, (xR, yT))

        if left_w > 0:
            out.paste(ML2, (xL, yM))
        out.paste(MM2, (xM, yM))
        if right_w > 0:
            out.paste(MR2, (xR, yM))

        if left_w > 0 and bot_h > 0:
            out.paste(BL, (xL, yB))
        if bot_h > 0:
            out.paste(BM2, (xM, yB))
        if right_w > 0 and bot_h > 0:
            out.paste(BR, (xR, yB))

        return out

    def apply_piecewise_stretch(self):
        if not self.image:
            return

        wh = self._read_wh()
        if not wh:
            return
        target_w, target_h = wh

        mode = self.pw_dir.get()
        img0 = self.image
        base_mode = img0.mode

        try:
            xa, xb, ya, yb = self._calc_pw_bounds_px()

            self._push_undo()

            if mode.startswith("横向"):
                out = self._piecewise_resize_h_px(img0, target_w, xa, xb)
                if self.pw_link_other.get():
                    out = out.resize((target_w, target_h), Image.Resampling.BILINEAR)

            elif mode.startswith("纵向"):
                out = self._piecewise_resize_v_px(img0, target_h, ya, yb)
                if self.pw_link_other.get():
                    out = out.resize((target_w, target_h), Image.Resampling.BILINEAR)

            else:
                out = self._nine_slice_resize_px(img0, target_w, target_h, xa, xb, ya, yb)

            if out.mode != base_mode:
                out = out.convert(base_mode)

            self.image = out
            self._after_image_changed(op_name="other")

        except Exception as e:
            try:
                if self.undo_stack:
                    self.undo_stack.pop()
            except Exception:
                pass
            self._refresh_undo_redo_state()
            messagebox.showerror("错误", f"分片拉伸失败：{e}")

        self._return_focus_to_canvas()

    # =========================
    # 调色
    # =========================
    def _ensure_rgb_alpha(self, img: Image.Image):
        if img.mode == "RGBA":
            r, g, b, a = img.split()
            rgb = Image.merge("RGB", (r, g, b))
            return rgb, a
        if img.mode != "RGB":
            img = img.convert("RGB")
        return img, None

    def _merge_rgb_alpha(self, rgb: Image.Image, alpha, base_mode: str):
        if alpha is None:
            return rgb if base_mode == "RGB" else rgb.convert(base_mode)
        rgba = Image.merge("RGBA", (*rgb.split(), alpha))
        return rgba

    def _apply_rgb_keep_alpha(self, func_rgb):
        if not self.image:
            return None
        base_mode = self.image.mode
        rgb, alpha = self._ensure_rgb_alpha(self.image)
        rgb2 = func_rgb(rgb)
        return self._merge_rgb_alpha(rgb2, alpha, base_mode)

    def apply_brightness(self):
        if not self.image:
            return
        try:
            k = float(self.var_brightness.get())
        except Exception:
            messagebox.showerror("错误", "亮度系数无效")
            return

        if k <= 0:
            messagebox.showerror("错误", "亮度系数必须 > 0")
            return

        self._push_undo()

        def _do(rgb):
            enh = ImageEnhance.Brightness(rgb)
            return enh.enhance(k)

        out = self._apply_rgb_keep_alpha(_do)
        if out is None:
            return
        self.image = out
        self._after_image_changed(op_name="other")

    def apply_whiten(self):
        if not self.image:
            return
        try:
            t = float(self.var_white.get()) / 100.0
        except Exception:
            t = 0.0
        t = max(0.0, min(1.0, t))

        if t <= 0:
            return

        self._push_undo()

        def _do(rgb):
            white = Image.new("RGB", rgb.size, (255, 255, 255))
            return Image.blend(rgb, white, t)

        out = self._apply_rgb_keep_alpha(_do)
        if out is None:
            return
        self.image = out
        self._after_image_changed(op_name="other")

    def apply_blacken(self):
        if not self.image:
            return
        try:
            t = float(self.var_black.get()) / 100.0
        except Exception:
            t = 0.0
        t = max(0.0, min(1.0, t))

        if t <= 0:
            return

        self._push_undo()

        def _do(rgb):
            black = Image.new("RGB", rgb.size, (0, 0, 0))
            return Image.blend(rgb, black, t)

        out = self._apply_rgb_keep_alpha(_do)
        if out is None:
            return
        self.image = out
        self._after_image_changed(op_name="other")

    # =========================
    # 旋转
    # =========================
    def _rotate_accumulated(self, deg: float):
        if not self.image:
            return

        self._push_undo()

        if self._last_op == "rotate" and self._rot_chain_base is not None:
            base = self._rot_chain_base
            total = self._rot_chain_total_deg + deg
        else:
            base = self.image.copy()
            total = deg

        self._rot_chain_base = base
        self._rot_chain_total_deg = total

        fill = (0, 0, 0, 0) if base.mode == "RGBA" else (255, 255, 255)
        rotated = base.rotate(total, expand=True, resample=Image.Resampling.BICUBIC, fillcolor=fill)

        self.image = rotated
        self._after_image_changed(op_name="rotate", keep_center=True)

    def rotate_quick(self, deg: int):
        if not self.image:
            return

        self._push_undo()
        self._mark_op("rotate")

        img = self.image
        if deg % 360 == 90:
            self.image = img.transpose(Image.Transpose.ROTATE_90)
        elif deg % 360 == -90 or deg % 360 == 270:
            self.image = img.transpose(Image.Transpose.ROTATE_270)
        elif deg % 360 == 180 or deg % 360 == -180:
            self.image = img.transpose(Image.Transpose.ROTATE_180)
        else:
            self.undo_stack.pop()
            self._refresh_undo_redo_state()
            self._rotate_accumulated(deg)
            return

        self._rot_chain_base = None
        self._rot_chain_total_deg = 0.0

        self.crop_box = None
        self._destroy_crop_items()
        self._checker_cache_size = None
        self._checker_cache_img = None

        self.ent_w.delete(0, tk.END)
        self.ent_h.delete(0, tk.END)
        self.ent_w.insert(0, str(self.image.size[0]))
        self.ent_h.insert(0, str(self.image.size[1]))

        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        nw, nh = self.image.size
        self._render_to_canvas(keep_view_point=(nw / 2, nh / 2, cw / 2, ch / 2))
        self._return_focus_to_canvas()

    def rotate_by_entry(self):
        if not self.image:
            return
        try:
            deg = float(self.ent_deg.get())
        except Exception:
            messagebox.showerror("错误", "角度必须是数字")
            return
        if abs(deg) < 1e-9:
            return
        self._rotate_accumulated(deg)
        self._return_focus_to_canvas()

    # =========================
    # 翻转
    # =========================
    def flip_horizontal(self):
        if not self.image:
            return
        self._push_undo()
        self.image = ImageOps.mirror(self.image)
        self._after_image_changed(op_name="other")

    def flip_vertical(self):
        if not self.image:
            return
        self._push_undo()
        self.image = ImageOps.flip(self.image)
        self._after_image_changed(op_name="other")

    # =========================
    # 画布扩展
    # =========================
    def pick_bg_color(self):
        c = colorchooser.askcolor(title="选择背景色", initialcolor=self.custom_bg)
        if c and c[1]:
            self.custom_bg = c[1]

    def _read_pad(self, ent: ttk.Entry) -> int:
        try:
            v = int(float(ent.get()))
            return max(0, v)
        except Exception:
            return 0

    def expand_canvas(self):
        if not self.image:
            return
        top = self._read_pad(self.ent_pad_top)
        bottom = self._read_pad(self.ent_pad_bottom)
        left = self._read_pad(self.ent_pad_left)
        right = self._read_pad(self.ent_pad_right)

        if top == bottom == left == right == 0:
            return

        self._push_undo()
        img = self.image
        iw, ih = img.size
        nw = iw + left + right
        nh = ih + top + bottom

        has_alpha = (img.mode == "RGBA")
        bg = self.bg_mode.get()

        if bg == "透明(如有Alpha)" and has_alpha:
            new_mode = "RGBA"
            fill = (0, 0, 0, 0)
        elif bg == "黑色":
            new_mode = "RGBA" if has_alpha else "RGB"
            fill = (0, 0, 0, 0) if new_mode == "RGBA" else (0, 0, 0)
        elif bg == "白色":
            new_mode = "RGBA" if has_alpha else "RGB"
            fill = (255, 255, 255, 255) if new_mode == "RGBA" else (255, 255, 255)
        else:
            hexv = self.custom_bg.lstrip("#")
            r = int(hexv[0:2], 16)
            g = int(hexv[2:4], 16)
            b = int(hexv[4:6], 16)
            new_mode = "RGBA" if has_alpha else "RGB"
            fill = (r, g, b, 255) if new_mode == "RGBA" else (r, g, b)

        new_img = Image.new(new_mode, (nw, nh), fill)

        if new_mode == "RGBA" and img.mode != "RGBA":
            img_to_paste = img.convert("RGBA")
        elif new_mode == "RGB" and img.mode != "RGB":
            if img.mode == "RGBA":
                bg_img = Image.new("RGBA", img.size, fill if len(fill) == 4 else (255, 255, 255, 255))
                img_to_paste = Image.alpha_composite(bg_img, img).convert("RGB")
            else:
                img_to_paste = img.convert("RGB")
        else:
            img_to_paste = img

        if new_mode == "RGBA" and img_to_paste.mode == "RGBA":
            new_img.paste(img_to_paste, (left, top), img_to_paste)
        else:
            new_img.paste(img_to_paste, (left, top))

        self.image = new_img
        self._after_image_changed(op_name="other")

    # =========================
    # 自动修剪透明边
    # =========================
    def trim_transparent(self):
        if not self.image:
            return
        if self.image.mode != "RGBA":
            messagebox.showinfo("提示", "当前图片不是 RGBA（没有透明通道），无法按透明边修剪。")
            return

        alpha = self.image.getchannel("A")
        bbox = alpha.getbbox()
        if not bbox:
            messagebox.showinfo("提示", "整张图都是透明的，无法修剪。")
            return

        self._push_undo()
        self.image = self.image.crop(bbox)
        self._after_image_changed(op_name="other")

    # =========================
    # 分割
    # =========================
    def _on_split_mode(self, event=None):
        if self.split_mode.get() == "自定义行列":
            self.custom_split.pack(fill=tk.X, padx=8, pady=(0, 8))
        else:
            self.custom_split.pack_forget()

    def split_image(self):
        if not self.image:
            return

        mode = self.split_mode.get()
        if mode == "4等分（2×2）":
            rows, cols = 2, 2
        elif mode == "9等分（3×3）":
            rows, cols = 3, 3
        elif mode == "16等分（4×4）":
            rows, cols = 4, 4
        else:
            try:
                rows = int(float(self.ent_rows.get()))
                cols = int(float(self.ent_cols.get()))
                if rows <= 0 or cols <= 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("错误", "自定义行列必须是 > 0 的数字")
                return

        out_dir = filedialog.askdirectory(title="选择保存目录")
        if not out_dir:
            return

        stem = self._base_stem()

        run_id = None
        for _ in range(50):
            cand = f"{secrets.randbelow(10000):04d}"
            test_path = os.path.join(out_dir, f"snapcrop_{stem}_r1_c1_{cand}.png")
            if not os.path.exists(test_path):
                run_id = cand
                break
        if run_id is None:
            run_id = f"{secrets.randbelow(10000):04d}"

        iw, ih = self.image.size
        w_per = iw // cols
        h_per = ih // rows

        count = 0
        for r in range(rows):
            for c in range(cols):
                x1 = c * w_per
                y1 = r * h_per
                x2 = (c + 1) * w_per if c < cols - 1 else iw
                y2 = (r + 1) * h_per if r < rows - 1 else ih

                piece = self.image.crop((x1, y1, x2, y2))

                name = f"snapcrop_{stem}_r{r+1}_c{c+1}_{run_id}.png"
                piece.save(os.path.join(out_dir, name), optimize=True)
                count += 1

        messagebox.showinfo("完成", f"已生成 {count} 张图片")
        self._return_focus_to_canvas()

    # =========================
    # 运行
    # =========================
    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    root = tk.Tk()
    app = SnapCrop(root)
    app.run()
