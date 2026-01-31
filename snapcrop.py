# SnapCrop - lightweight desktop image crop & edit tool
# 说明：本项目在 GPT 的协助下完成（部分功能思路与代码结构由 GPT 提供建议）。

import os
import secrets  # 用于生成更可靠的随机数（这里用来做 4 位随机后缀）
import webbrowser
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser
from PIL import Image, ImageTk, ImageOps


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

        # ====== UI ======
        self._build_style()
        self._build_layout()
        self._bind_shortcuts()
        self._set_ui_enabled(False)

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

        # 主体：左面板 + 右 canvas
        self.main = ttk.Frame(root, style="App.TFrame")
        self.main.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        self.left = ttk.Frame(self.main, style="Panel.TFrame", width=360)
        self.left.pack(side=tk.LEFT, fill=tk.Y)
        self.left.pack_propagate(False)

        self.right = ttk.Frame(self.main, style="Panel.TFrame")
        self.right.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # 左：Notebook
        self.nb = ttk.Notebook(self.left)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        self.tab_transform = ttk.Frame(self.nb, style="Panel.TFrame")
        self.tab_crop = ttk.Frame(self.nb, style="Panel.TFrame")
        self.tab_split = ttk.Frame(self.nb, style="Panel.TFrame")
        self.tab_ops = ttk.Frame(self.nb, style="Panel.TFrame")
        self.tab_info = ttk.Frame(self.nb, style="Panel.TFrame")  # 新增：详情/代码页

        self.nb.add(self.tab_transform, text="缩放")
        self.nb.add(self.tab_crop, text="裁剪")
        self.nb.add(self.tab_ops, text="变换")
        self.nb.add(self.tab_split, text="分割")
        self.nb.add(self.tab_info, text=self.INFO_TAB_TITLE)  # 你想叫“代码”就改 INFO_TAB_TITLE

        # ---- Transform ----
        lf = ttk.Labelframe(self.tab_transform, text="缩放 / 拉伸")
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

        # ---- Crop ----
        lf_ratio = ttk.Labelframe(self.tab_crop, text="裁剪比例")
        lf_ratio.pack(fill=tk.X, padx=10, pady=(10, 6))

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

        ttk.Label(
            self.tab_crop,
            text="比例手感（已优化）：\n"
                 "- 固定比例时，拖动边(N/S/E/W)默认“以中心对称缩放”（更像PS）\n"
                 "- Shift：自由模式下临时 1:1；已有框时临时保持当前比例\n"
                 "- Space：拖拽边/角时临时“移动裁剪框（保持尺寸）”（用于卡边时顺滑挪动）\n"
                 "- 方向键：移动（Shift=10px）\n"
                 "- Ctrl + 方向键：向外扩展；Ctrl+Shift+方向键：向内收缩\n"
                 "- Enter：应用裁剪；Esc：清除裁剪框\n"
                 "- 滚轮：缩放；中键/右键拖拽：平移\n",
            justify=tk.LEFT
        ).pack(fill=tk.X, padx=12, pady=(6, 10))

        lf2 = ttk.Labelframe(self.tab_crop, text="边缘裁剪（px / %）")
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

        # ---- Ops (Rotate/Flip/Canvas/Trim) ----
        lf_rot = ttk.Labelframe(self.tab_ops, text="旋转")
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

        lf_flip = ttk.Labelframe(self.tab_ops, text="翻转")
        lf_flip.pack(fill=tk.X, padx=10, pady=(0, 8))

        rowf = ttk.Frame(lf_flip)
        rowf.pack(fill=tk.X, padx=8, pady=8)
        self.btn_flip_h = ttk.Button(rowf, text="水平翻转", command=self.flip_horizontal, style="Tool.TButton")
        self.btn_flip_h.pack(side=tk.LEFT, padx=(0, 8))
        self.btn_flip_v = ttk.Button(rowf, text="垂直翻转", command=self.flip_vertical, style="Tool.TButton")
        self.btn_flip_v.pack(side=tk.LEFT)

        # ---- Canvas Expand ----
        lf_canvas = ttk.Labelframe(self.tab_ops, text="画布扩展（Padding px）")
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

        lf_trim = ttk.Labelframe(self.tab_ops, text="自动修剪")
        lf_trim.pack(fill=tk.X, padx=10, pady=(0, 10))

        self.btn_trim_alpha = ttk.Button(lf_trim, text="自动修剪透明边（Trim Alpha）", command=self.trim_transparent, style="Accent.TButton")
        self.btn_trim_alpha.pack(fill=tk.X, padx=8, pady=10)

        # ---- Split ----
        lf3 = ttk.Labelframe(self.tab_split, text="等分分割")
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

    def _build_info_tab(self):
        lf = ttk.Labelframe(self.tab_info, text="项目 / Project")
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

        # ===== 修复焦点/空格 bug 的关键绑定 =====
        c.configure(takefocus=True)  # 允许 Canvas 拿键盘焦点
        c.bind("<KeyPress-space>", self._on_space_press)     # Space 只在 Canvas 上生效
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

    def _set_shift(self, v: bool):
        self.shift_down = v

    def _set_ctrl(self, v: bool):
        self.ctrl_down = v

    # ===== 修复焦点/空格 bug：Space 只由 Canvas 处理，并阻断事件继续传播 =====
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
            self.combo_aspect, self.ent_aspect_w, self.ent_aspect_h,
            self.ent_deg, self.btn_rot_apply, self.btn_rot_l, self.btn_rot_r, self.btn_rot_180,
            self.btn_flip_h, self.btn_flip_v,
            self.ent_pad_top, self.ent_pad_bottom, self.ent_pad_left, self.ent_pad_right,
            self.combo_bg, self.btn_pick_bg, self.btn_expand, self.btn_trim_alpha
        ]:
            try:
                w.configure(state=st)
            except Exception:
                pass
        # 注意：详情页里的“打开网页”按钮不依赖图片，不在这里禁用

    # =========================
    # Rotate-chain helpers (fix runaway size)
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
    # 文件命名辅助（用于分割输出：snapcrop_原图名_..._四位随机数.png）
    # =========================
    def _safe_stem(self, s: str) -> str:
        """
        把原文件名“净化”为更安全的形式（避免空格/符号导致跨平台路径问题）
        - 允许：字母数字、-、_
        - 其它字符：替换为 _
        """
        s = (s or "").strip() or "image"
        return "".join(ch if (ch.isalnum() or ch in ("-", "_")) else "_" for ch in s)

    def _base_stem(self) -> str:
        """
        优先使用打开图片的文件名（不含扩展名）。
        如果当前没有 file_path，则回退为 "image"。
        """
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

    def _get_selected_ratio(self):
        m = self.aspect_mode.get()
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
        self._update_status()

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

            self.ent_w.delete(0, tk.END)
            self.ent_h.delete(0, tk.END)
            self.ent_w.insert(0, str(img.size[0]))
            self.ent_h.insert(0, str(img.size[1]))

            self._checker_cache_size = None
            self._checker_cache_img = None

            self._reset_rotate_chain()
            self._set_ui_enabled(True)
            self._refresh_undo_redo_state()
            self._render_to_canvas()
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

    def redo(self):
        if not self.redo_stack or not self.image:
            return
        self.undo_stack.append(self.image.copy())
        self.image = self.redo_stack.pop()
        self._after_image_changed(op_name="other")

    def _after_image_changed(self, op_name="other", keep_center=False):
        # 任何“非旋转”操作，都终止旋转链
        self._mark_op(op_name)

        self.crop_box = None
        self._destroy_crop_items()
        self._checker_cache_size = None
        self._checker_cache_img = None

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
        self.canvas.focus_set()  # 修复：避免空格触发按钮/输入框
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
            return

        self._ensure_crop_items()

        iw, ih = self.image.size
        x1, y1, x2, y2 = self.crop_box

        cx1, cy1 = self._image_to_canvas(x1, y1)
        cx2, cy2 = self._image_to_canvas(x2, y2)
        w = int(round(iw * self.scale))
        h = int(round(ih * self.scale))

        self.canvas.coords(self.crop_rect_id, cx1, cy1, cx2, cy2)

        self.canvas.coords(self.shade_ids[0], 0, 0, w, cy1)      # 上
        self.canvas.coords(self.shade_ids[1], 0, cy2, w, h)      # 下
        self.canvas.coords(self.shade_ids[2], 0, cy1, cx1, cy2)  # 左
        self.canvas.coords(self.shade_ids[3], cx2, cy1, w, cy2)  # 右

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

    def clear_crop(self):
        self.crop_box = None
        self._destroy_crop_items()
        self._update_status()

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
        """固定比例 + 拖边：保持中心(cx,cy)，对称改变宽/高（PS风格）"""
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
        """角点缩放：保持对角点固定（原有逻辑，够用）"""
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

        # ===== 修复焦点 bug：只要开始在画布上操作，就把焦点切回 Canvas =====
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
            h = self._drag_handle
            ratio = self._active_ratio_for_drag(is_new=False)

            if ratio is not None and h in ("n", "s", "e", "w") and self._resize_base_center:
                rcx, rcy = self._resize_base_center
                self.crop_box = self._side_center_symmetric_box(rcx, rcy, h, ix, iy, ratio)
                self._update_crop_overlay()
                self._drag_last = (ix, iy)
                return

            if h == "nw":
                x1, y1 = ix, iy
            elif h == "n":
                y1 = iy
            elif h == "ne":
                x2, y1 = ix, iy
            elif h == "w":
                x1 = ix
            elif h == "e":
                x2 = ix
            elif h == "sw":
                x1, y2 = ix, iy
            elif h == "s":
                y2 = iy
            elif h == "se":
                x2, y2 = ix, iy

            box = self._clamp_box((x1, y1, x2, y2))
            if ratio is not None and h in ("nw", "ne", "sw", "se"):
                box = self._apply_ratio_resize_corner(box, h, ratio)

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

    def apply_crop(self):
        if not self.image or not self.crop_box:
            return
        x1, y1, x2, y2 = self.crop_box
        if x2 <= x1 or y2 <= y1:
            return
        self._push_undo()
        self.image = self.image.crop((x1, y1, x2, y2))
        self._after_image_changed(op_name="other")

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
        """
        分割并保存：
        - 文件名格式：snapcrop_<原图名>_r1_c1_1234.png
        - 同一次分割使用同一个 4 位随机数 run_id（更整齐）
        - 下一次分割 run_id 会变，避免覆盖同名文件
        """
        if not self.image:
            return

        # 1) 读分割模式
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

        # 2) 选择输出目录
        out_dir = filedialog.askdirectory(title="选择保存目录")
        if not out_dir:
            return

        # 3) 生成本次分割的“基础名”和 4 位随机后缀
        stem = self._base_stem()

        # 生成 run_id：尽量避免极小概率碰撞（同目录已有同名文件时就再随机一次）
        run_id = None
        for _ in range(50):
            cand = f"{secrets.randbelow(10000):04d}"  # 0000~9999
            test_path = os.path.join(out_dir, f"snapcrop_{stem}_r1_c1_{cand}.png")
            if not os.path.exists(test_path):
                run_id = cand
                break
        if run_id is None:
            # 理论上非常难到这里；作为兜底，直接用一个随机值
            run_id = f"{secrets.randbelow(10000):04d}"

        # 4) 计算每块尺寸并保存
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

                # 文件名：snapcrop_原图名_rX_cY_1234.png
                name = f"snapcrop_{stem}_r{r+1}_c{c+1}_{run_id}.png"
                piece.save(os.path.join(out_dir, name), optimize=True)
                count += 1

        messagebox.showinfo("完成", f"已生成 {count} 张图片")

    # =========================
    # 运行
    # =========================
    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    root = tk.Tk()
    app = SnapCrop(root)
    app.run()
