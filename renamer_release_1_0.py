# -*- coding: utf-8 -*-
"""
Renamer v11

Outil Tkinter de renommage de fichiers OU dossiers :
- mode sombre propre
- choix du dossier de travail
- chargement non bloquant sans popup de chargement
- inclusion optionnelle des sous-dossiers, appliquée uniquement au clic sur "Charger"
- modes exclusifs : renommage fichiers OU renommage dossiers
- filtres appliqués uniquement au clic sur "Appliquer filtres"
- filtres par texte/nom/chemin relatif et par extension pour les fichiers
- recherche/remplacement avec joker * façon Excel
- interdiction de la recherche globale "*" seule
- tri alphabétique avec flèche visible dans les en-têtes
- une seule colonne triée active à la fois
- recherche/remplacement limité strictement à la vue filtrée active
- bouton de renommage final séparé, visible et coloré
- édition directe des nouveaux noms par double-clic dans le tableau
- validations anti-conflits
- log intégré
- infobulles explicatives hors tableau
- bouton "À propos"
- fenêtre de confirmation détaillée avant renommage

Aucune dépendance externe : Python + Tkinter uniquement.
"""

import ctypes
import os
import queue
import re
import sys
import threading
import uuid
from pathlib import Path
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_VERSION = "Release 1.0"
APP_TITLE = "Renamer - Release 1.0"
CHECKED = "☑"
UNCHECKED = "☐"
SORT_ASC = " ▲"
SORT_DESC = " ▼"
WINDOWS_INVALID_CHARS = set('<>:"/\\|?*')
WINDOWS_RESERVED_NAMES = {
    "CON", "PRN", "AUX", "NUL",
    "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9",
    "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9",
}


class Tooltip:
    """Infobulle simple pour Tkinter/ttk, sans dépendance externe."""

    def __init__(self, widget, text: str, delay: int = 450) -> None:
        self.widget = widget
        self.text = text
        self.delay = delay
        self.after_id = None
        self.tip = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def _schedule(self, _event=None) -> None:
        self._cancel()
        self.after_id = self.widget.after(self.delay, self._show)

    def _cancel(self) -> None:
        if self.after_id:
            self.widget.after_cancel(self.after_id)
            self.after_id = None

    def _show(self) -> None:
        if self.tip or not self.text:
            return
        x = self.widget.winfo_rootx() + 18
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 8
        self.tip = tk.Toplevel(self.widget)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry(f"+{x}+{y}")
        label = tk.Label(
            self.tip,
            text=self.text,
            justify="left",
            bg="#111827",
            fg="#f9fafb",
            relief="solid",
            borderwidth=1,
            padx=8,
            pady=5,
            wraplength=430,
        )
        label.pack()

    def _hide(self, _event=None) -> None:
        self._cancel()
        if self.tip:
            self.tip.destroy()
            self.tip = None


class RenameItem:
    """Représente un fichier ou un dossier chargé et son état de renommage."""

    def __init__(self, path: Path, base_dir: Path, is_dir: bool) -> None:
        self.path = path
        self.base_dir = base_dir
        self.is_dir = is_dir
        self.checked = True
        self.manual_name = ""
        self.preview_name = path.name

    @property
    def kind(self) -> str:
        return "Dossier" if self.is_dir else "Fichier"

    @property
    def rel_path(self) -> str:
        return str(self.path.relative_to(self.base_dir))

    @property
    def parent_folder(self) -> str:
        rel_parent = self.path.parent.relative_to(self.base_dir)
        return "./" if str(rel_parent) == "." else str(rel_parent)

    @property
    def ext(self) -> str:
        return "" if self.is_dir else self.path.suffix.lower()

    @property
    def depth(self) -> int:
        return len(self.path.relative_to(self.base_dir).parts)

    def target_name(self) -> str:
        return self.manual_name.strip() or self.preview_name

    def target_path(self) -> Path:
        return self.path.with_name(self.target_name())


class RenamerDarkUI:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        # La fenêtre reste masquée pendant la construction de l'interface.
        # Cela évite le flash/bloc blanc observé au lancement depuis cmd sous Windows.
        self.root.withdraw()
        self.root.geometry("1320x800")
        self.root.minsize(1100, 690)
        self._enable_windows_dark_titlebar()

        self.base_dir: Path | None = None
        self.items: list[RenameItem] = []
        self.visible_ids: list[str] = []
        self.iid_to_item: dict[str, RenameItem] = {}
        self.item_status: dict[RenameItem, str] = {}
        self.load_queue: queue.Queue = queue.Queue()
        self.loading = False
        self.edit_entry: ttk.Entry | None = None
        self.editing_iid: str | None = None
        self._clamp_job: str | None = None
        self.table_fixed_widths: dict[str, int] = {}
        self.table_min_widths: dict[str, int] = {}

        self.folder_var = tk.StringVar()
        self.recursive_var = tk.BooleanVar(value=False)
        self.mode_var = tk.StringVar(value="files")
        self.show_checked_var = tk.BooleanVar(value=True)
        self.show_unchecked_var = tk.BooleanVar(value=True)

        self.filter_text_var = tk.StringVar()
        self.filter_ext_var = tk.StringVar()
        self.applied_filter_text = ""
        self.applied_filter_exts: list[str] = []

        self.search_var = tk.StringVar()
        self.replace_var = tk.StringVar()
        self.case_var = tk.BooleanVar(value=False)
        self.status_var = tk.StringVar(value="Choisissez un dossier, un mode, puis cliquez sur Charger.")

        self.sort_column = "parent"
        self.sort_reverse = False
        self.column_titles = {
            "check": "✓",
            "kind": "Type",
            "parent": "Emplacement",
            "name": "Nom actuel",
            "ext": "Ext.",
            "newname": "Nouveau nom",
            "status": "Statut",
            "action": "Annuler",
        }

        self._build_style()
        self._build_ui()
        self._bind_events()
        self._install_tooltips()
        self._show_ready_window()

    def _show_ready_window(self) -> None:
        """Affiche la fenêtre uniquement quand le thème sombre et les widgets sont prêts."""
        self.root.update_idletasks()
        self._clamp_table_columns()
        self.root.deiconify()
        self.root.lift()
        self._enable_windows_dark_titlebar()
        self._force_initial_dark_paint()

    def _force_initial_dark_paint(self) -> None:
        """Force quelques rafraîchissements initiaux pour éviter un rendu blanc au premier affichage."""
        self.root.configure(bg=self.colors["bg"])
        self.rename_tab.configure(style="TFrame")
        for delay in (0, 60, 180):
            self.root.after(delay, self._refresh_dark_paint_once)

    def _refresh_dark_paint_once(self) -> None:
        try:
            self.root.configure(bg=self.colors["bg"])
            self.root.update_idletasks()
            self._clamp_table_columns()
        except Exception:
            pass

    def _schedule_clamp_table_columns(self, _event=None) -> None:
        if self._clamp_job is not None:
            try:
                self.root.after_cancel(self._clamp_job)
            except Exception:
                pass
        self._clamp_job = self.root.after_idle(self._clamp_table_columns)

    def _clamp_table_columns(self) -> None:
        """Adapte les colonnes pour que le tableau reste dans la largeur visible."""
        self._clamp_job = None
        if not hasattr(self, "tree"):
            return

        width = self.tree.winfo_width()
        if width <= 1:
            return

        # Petite marge pour les bordures internes du Treeview. La barre verticale est hors Treeview.
        available = max(width - 4, 1)
        fixed_total = sum(self.table_fixed_widths.values())
        variable_columns = ("parent", "name", "newname", "status")
        weights = {"parent": 0.23, "name": 0.27, "newname": 0.32, "status": 0.18}

        variable_available = max(available - fixed_total, sum(self.table_min_widths.values()))
        computed: dict[str, int] = dict(self.table_fixed_widths)
        used = 0
        for col in variable_columns[:-1]:
            value = max(self.table_min_widths[col], int(variable_available * weights[col]))
            computed[col] = value
            used += value
        last = variable_columns[-1]
        computed[last] = max(self.table_min_widths[last], variable_available - used)

        # Si les minimums dépassent malgré tout la place disponible, on réduit proportionnellement
        # les colonnes variables en conservant les colonnes d'action/état lisibles.
        total = sum(computed.values())
        if total > available:
            overflow = total - available
            reducible_columns = ("parent", "name", "newname", "status")
            while overflow > 0:
                changed = False
                for col in reducible_columns:
                    if overflow <= 0:
                        break
                    floor = max(70, self.table_min_widths[col] - 70)
                    if computed[col] > floor:
                        computed[col] -= 1
                        overflow -= 1
                        changed = True
                if not changed:
                    break

        for col, value in computed.items():
            self.tree.column(col, width=max(1, int(value)), stretch=False)

    def _enable_windows_dark_titlebar(self) -> None:
        """Active le titre/bordure sombre de la fenêtre sur Windows 10/11 lorsque disponible."""
        if sys.platform != "win32":
            return
        try:
            self.root.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id()) or self.root.winfo_id()
            value = ctypes.c_int(1)
            for attribute in (20, 19):
                result = ctypes.windll.dwmapi.DwmSetWindowAttribute(
                    ctypes.c_void_p(hwnd),
                    ctypes.c_int(attribute),
                    ctypes.byref(value),
                    ctypes.sizeof(value),
                )
                if result == 0:
                    break
        except Exception:
            pass

    def _enable_windows_dark_titlebar_for_window(self, window: tk.Toplevel) -> None:
        if sys.platform != "win32":
            return
        try:
            window.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(window.winfo_id()) or window.winfo_id()
            value = ctypes.c_int(1)
            for attribute in (20, 19):
                result = ctypes.windll.dwmapi.DwmSetWindowAttribute(
                    ctypes.c_void_p(hwnd),
                    ctypes.c_int(attribute),
                    ctypes.byref(value),
                    ctypes.sizeof(value),
                )
                if result == 0:
                    break
        except Exception:
            pass

    def _build_style(self) -> None:
        self.colors = {
            "bg": "#1f232a",
            "panel": "#272c34",
            "panel2": "#303744",
            "text": "#f3f4f6",
            "entry": "#111827",
            "entry_border": "#4b5563",
            "button": "#3b4658",
            "button_active": "#52627a",
            "danger": "#b91c1c",
            "danger_active": "#dc2626",
            "tree": "#151a21",
            "tree_alt": "#1b222c",
            "tree_heading": "#2e3746",
            "tree_heading_active": "#3d4a5e",
            "select": "#2563eb",
        }

        self.root.configure(bg=self.colors["bg"])
        style = ttk.Style()
        style.theme_use("clam")
        style.configure(".", background=self.colors["bg"], foreground=self.colors["text"])


        style.configure("TFrame", background=self.colors["bg"])
        style.configure("Panel.TFrame", background=self.colors["panel"])
        style.configure("TLabel", background=self.colors["bg"], foreground=self.colors["text"])
        style.configure("Panel.TLabel", background=self.colors["panel"], foreground=self.colors["text"])

        style.configure("TCheckbutton", background=self.colors["panel"], foreground=self.colors["text"], focuscolor=self.colors["panel"])
        style.map("TCheckbutton", background=[("active", self.colors["panel2"])], foreground=[("active", "#ffffff"), ("selected", "#ffffff")])

        style.configure("TButton", background=self.colors["button"], foreground=self.colors["text"], borderwidth=1, padding=(9, 5))
        style.map("TButton", background=[("active", self.colors["button_active"]), ("pressed", "#2c3442")], foreground=[("active", "#ffffff"), ("pressed", "#ffffff")])
        style.configure("Danger.TButton", background=self.colors["danger"], foreground="#ffffff", borderwidth=1, padding=(14, 7), font=("Segoe UI", 10, "bold"))
        style.map("Danger.TButton", background=[("active", self.colors["danger_active"]), ("pressed", "#7f1d1d")], foreground=[("active", "#ffffff"), ("pressed", "#ffffff")])

        style.configure(
            "TEntry",
            fieldbackground=self.colors["entry"],
            foreground=self.colors["text"],
            insertcolor=self.colors["text"],
            bordercolor=self.colors["entry_border"],
            lightcolor=self.colors["entry_border"],
            darkcolor=self.colors["entry_border"],
        )
        style.map("TEntry", fieldbackground=[("focus", "#0f172a"), ("active", "#0f172a")], foreground=[("focus", self.colors["text"])])

        style.configure(
            "Treeview",
            background=self.colors["tree"],
            foreground=self.colors["text"],
            fieldbackground=self.colors["tree"],
            rowheight=27,
            bordercolor="#374151",
            borderwidth=1,
        )
        style.configure("Treeview.Heading", background=self.colors["tree_heading"], foreground=self.colors["text"], relief="raised", padding=(7, 5))
        style.map("Treeview", background=[("selected", self.colors["select"])], foreground=[("selected", "#ffffff")])
        style.map("Treeview.Heading", background=[("active", self.colors["tree_heading_active"])], foreground=[("active", "#ffffff")])

        style.configure("Vertical.TScrollbar", background=self.colors["panel2"], troughcolor=self.colors["bg"], arrowcolor=self.colors["text"])
    def _build_ui(self) -> None:
        self.rename_tab = ttk.Frame(self.root, padding=10)
        self.rename_tab.pack(fill="both", expand=True)
        self._build_rename_tab()

    def _build_rename_tab(self) -> None:
        top = ttk.Frame(self.rename_tab, style="Panel.TFrame", padding=10)
        top.pack(fill="x")

        ttk.Label(top, text="Dossier :", style="Panel.TLabel").pack(side="left")
        ttk.Entry(top, textvariable=self.folder_var, width=48).pack(side="left", fill="x", expand=True, padx=8)
        ttk.Button(top, text="Parcourir", command=self.choose_folder).pack(side="left")
        self.load_button = ttk.Button(top, text="Charger", command=self.load_items)
        self.load_button.pack(side="left", padx=(8, 14))

        ttk.Checkbutton(top, text="Inclure sous-dossiers", variable=self.recursive_var).pack(side="left", padx=(0, 10))
        ttk.Checkbutton(top, text="Renommer fichiers", variable=self.mode_var, onvalue="files", offvalue="folders").pack(side="left")
        ttk.Checkbutton(top, text="Renommer dossiers", variable=self.mode_var, onvalue="folders", offvalue="files").pack(side="left", padx=(8, 12))
        ttk.Button(top, text="À propos", command=self.show_about).pack(side="left")


        options = ttk.Frame(self.rename_tab, style="Panel.TFrame", padding=(10, 8))
        options.pack(fill="x", pady=(8, 0))
        ttk.Label(options, text="Filtre texte/nom :", style="Panel.TLabel").pack(side="left")
        ttk.Entry(options, width=34, textvariable=self.filter_text_var).pack(side="left", padx=(5, 14))
        ttk.Label(options, text="Extension(s) fichiers :", style="Panel.TLabel").pack(side="left")
        ttk.Entry(options, width=26, textvariable=self.filter_ext_var).pack(side="left", padx=5)
        ttk.Button(options, text="Appliquer filtres", command=self.apply_filters).pack(side="left", padx=8)
        ttk.Button(options, text="Réinitialiser", command=self.reset_filters).pack(side="left")

        rename = ttk.Frame(self.rename_tab, style="Panel.TFrame", padding=(10, 8))
        rename.pack(fill="x", pady=(8, 0))
        ttk.Label(rename, text="Rechercher :", style="Panel.TLabel").pack(side="left")
        ttk.Entry(rename, width=30, textvariable=self.search_var).pack(side="left", padx=5)
        ttk.Label(rename, text="Remplacer par :", style="Panel.TLabel").pack(side="left", padx=(10, 5))
        ttk.Entry(rename, width=30, textvariable=self.replace_var).pack(side="left")
        ttk.Checkbutton(rename, text="Respecter casse", variable=self.case_var, command=self.update_preview_and_refresh).pack(side="left", padx=12)
        ttk.Button(rename, text="Aperçu", command=self.update_preview_and_refresh).pack(side="left", padx=8)


        middle = ttk.Frame(self.rename_tab, padding=(0, 8, 0, 8))
        middle.pack(fill="both", expand=True)

        columns = ("check", "kind", "parent", "name", "ext", "newname", "status", "action")
        self.tree = ttk.Treeview(middle, columns=columns, show="headings", selectmode="browse")
        self.tree.tag_configure("odd", background=self.colors["tree"])
        self.tree.tag_configure("even", background=self.colors["tree_alt"])
        self.tree.tag_configure("renamed", foreground="#f59e0b")
        self.tree.tag_configure("undo_available", foreground="#fb923c")

        for col in columns:
            self.tree.heading(col, text=self.column_titles[col], command=lambda c=col: self.sort_by_column(c))

        self.table_fixed_widths = {"check": 48, "kind": 85, "ext": 75, "action": 135}
        self.table_min_widths = {"parent": 150, "name": 190, "newname": 210, "status": 130}
        self.tree.column("check", width=48, minwidth=48, anchor="center", stretch=False)
        self.tree.column("kind", width=85, minwidth=85, anchor="center", stretch=False)
        self.tree.column("parent", width=245, minwidth=150, stretch=False)
        self.tree.column("name", width=320, minwidth=190, stretch=False)
        self.tree.column("ext", width=75, minwidth=75, anchor="center", stretch=False)
        self.tree.column("newname", width=340, minwidth=210, stretch=False)
        self.tree.column("status", width=180, minwidth=130, stretch=False)
        self.tree.column("action", width=135, minwidth=135, anchor="center", stretch=False)
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.bind("<Configure>", self._schedule_clamp_table_columns, add="+")

        scroll = ttk.Scrollbar(middle, orient="vertical", command=self.tree.yview, style="Vertical.TScrollbar")
        self.tree.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")

        actions = ttk.Frame(self.rename_tab, style="Panel.TFrame", padding=(10, 8))
        actions.pack(fill="x")
        self.rename_button = ttk.Button(actions, text="⚠ RENOMMER LA SÉLECTION VISIBLE", command=self.rename_checked, style="Danger.TButton")
        self.rename_button.pack(side="left")
        ttk.Checkbutton(actions, text="Afficher cochés", variable=self.show_checked_var, command=self.update_preview_and_refresh).pack(side="left", padx=(18, 4))
        ttk.Checkbutton(actions, text="Afficher décochés", variable=self.show_unchecked_var, command=self.update_preview_and_refresh).pack(side="left", padx=(4, 12))
        ttk.Button(actions, text="Tout cocher visible", command=lambda: self.set_visible_checked(True)).pack(side="left", padx=(0, 8))
        ttk.Button(actions, text="Tout décocher visible", command=lambda: self.set_visible_checked(False)).pack(side="left", padx=8)
        ttk.Button(actions, text="Inverser visible", command=self.invert_visible_checked).pack(side="left")
        ttk.Label(actions, textvariable=self.status_var, style="Panel.TLabel").pack(side="right")

        log_frame = ttk.Frame(self.rename_tab, style="Panel.TFrame", padding=10)
        log_frame.pack(fill="both", pady=(8, 0))
        ttk.Label(log_frame, text="Log :", style="Panel.TLabel").pack(anchor="w")
        self.log = tk.Text(
            log_frame,
            height=6,
            bg="#0f172a",
            fg="#e5e7eb",
            insertbackground="#ffffff",
            selectbackground="#2563eb",
            selectforeground="#ffffff",
            relief="flat",
            padx=8,
            pady=6,
        )
        self.log.pack(fill="both", expand=False, pady=(5, 0))

        self._update_sort_headers()

    def show_about(self) -> None:
        """Fenêtre À propos sous forme de dialogue, sans zone de texte éditable."""
        dialog = tk.Toplevel(self.root)
        dialog.title(f"À propos - {APP_TITLE}")
        dialog.configure(bg=self.colors["bg"])
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        self._enable_windows_dark_titlebar_for_window(dialog)

        outer = tk.Frame(dialog, bg=self.colors["bg"], padx=18, pady=16)
        outer.pack(fill="both", expand=True)

        tk.Label(
            outer,
            text=APP_TITLE,
            bg=self.colors["bg"],
            fg=self.colors["text"],
            font=("Segoe UI", 16, "bold"),
        ).pack(anchor="w")
        tk.Label(
            outer,
            text="Version stabilisée avec édition directe, annulation par ligne et filtres avancés.",
            bg=self.colors["bg"],
            fg="#cbd5e1",
            font=("Segoe UI", 10),
        ).pack(anchor="w", pady=(2, 12))

        content = tk.Frame(outer, bg=self.colors["panel"], padx=14, pady=12)
        content.pack(fill="both", expand=True)

        def section(title: str, lines: list[str]) -> None:
            tk.Label(
                content,
                text=title,
                bg=self.colors["panel"],
                fg="#ffffff",
                font=("Segoe UI", 10, "bold"),
            ).pack(anchor="w", pady=(8, 2))
            for line in lines:
                tk.Label(
                    content,
                    text=f"• {line}",
                    bg=self.colors["panel"],
                    fg=self.colors["text"],
                    font=("Segoe UI", 9),
                    justify="left",
                    wraplength=680,
                ).pack(anchor="w", padx=(12, 0), pady=1)

        section("Fonctionnement", [
            "Choisir un dossier, sélectionner le mode fichiers ou dossiers, puis cliquer sur Charger.",
            "Les filtres texte/nom et extension s'appliquent uniquement avec le bouton Appliquer filtres.",
            "Le tableau reste automatiquement clampé dans la largeur de la fenêtre.",
        ])
        section("Recherche et filtres avec joker *", [
            "Le joker * fonctionne dans Rechercher, Filtre texte/nom et Extension(s) fichiers.",
            "Exemples : plan*, *plan, plan*final, d*, *wg.",
            "Le caractère * seul est interdit pour éviter une action globale involontaire.",
        ])
        section("Édition et annulation", [
            "Double-cliquer dans la colonne Nouveau nom pour éditer directement une cellule.",
            "Le bouton [ ↶ ANNULER ] apparaît dès qu'un nom diffère du nom d'origine.",
            "Le bouton [ ↶ ANNULER ] apparaît aussi en cas de Conflit doublon pour restaurer le nom d'origine.",
        ])
        section("Statuts", [
            "Inchangé : le nouveau nom est identique au nom d'origine.",
            "Renommé : le nouveau nom est différent du nom d'origine.",
            "Les statuts ne dépendent pas de l'affichage, de la sélection ou du filtrage visible.",
        ])
        section("Renommage final", [
            "Le bouton RENOMMER LA SÉLECTION VISIBLE affiche une confirmation détaillée avant toute action réelle.",
            "Les validations anti-conflits et anti-noms Windows invalides restent actives avant le renommage.",
        ])

        bottom = tk.Frame(outer, bg=self.colors["bg"])
        bottom.pack(fill="x", pady=(14, 0))
        ttk.Button(bottom, text="Fermer", command=dialog.destroy).pack(side="right")

        dialog.update_idletasks()
        width = max(760, dialog.winfo_reqwidth())
        height = max(560, dialog.winfo_reqheight())
        x = self.root.winfo_rootx() + max(0, (self.root.winfo_width() - width) // 2)
        y = self.root.winfo_rooty() + max(0, (self.root.winfo_height() - height) // 2)
        dialog.geometry(f"{width}x{height}+{x}+{y}")
        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.wait_window()

    def _bind_events(self) -> None:
        self.tree.bind("<Button-1>", self.on_tree_click)
        self.tree.bind("<Double-1>", self.on_tree_double_click)
        self.root.bind("<Configure>", self._schedule_clamp_table_columns, add="+")
        self.root.bind("<Map>", lambda _event: self._force_initial_dark_paint(), add="+")

    def _install_tooltips(self) -> None:
        tips_by_text = {
            "Dossier :": "Chemin du dossier de travail. Utilisez Parcourir, puis Charger.",
            "Parcourir": "Ouvre l'explorateur pour sélectionner le dossier de travail. Ne charge rien automatiquement.",
            "Charger": "Charge les fichiers ou dossiers selon le mode choisi et l'option sous-dossiers. Le chargement se fait en arrière-plan.",
            "Inclure sous-dossiers": "Si coché, le prochain clic sur Charger inclut aussi tous les sous-dossiers.",
            "Renommer fichiers": "Active le mode fichiers. Exclusif avec le mode dossiers.",
            "Renommer dossiers": "Active le mode dossiers. Exclusif avec le mode fichiers.",
            "À propos": "Ouvre la fenêtre d'aide et d'explication de cette version.",
            "Filtre texte/nom :": "Texte recherché dans le nom et le chemin relatif. Joker * possible ; * seul est interdit. Appliqué seulement via Appliquer filtres.",
            "Extension(s) fichiers :": "Extensions à afficher en mode fichiers, par exemple pdf, .dwg, jpg png, d* ou *wg. Le joker * seul est interdit.",
            "Appliquer filtres": "Applique les filtres saisis. La saisie seule ne modifie pas la vue.",
            "Réinitialiser": "Vide les filtres texte/extension et réaffiche les éléments chargés.",
            "Rechercher :": "Texte à trouver dans les noms visibles. Le caractère * sert de joker façon Excel.",
            "Remplacer par :": "Texte qui remplacera la partie trouvée dans les noms visibles uniquement.",
            "Respecter casse": "Si coché, distingue majuscules et minuscules. Exemple : Plan différent de plan.",
            "Aperçu": "Met à jour la colonne Nouveau nom sans renommer réellement.",
            "⚠ RENOMMER LA SÉLECTION VISIBLE": "Ouvre une confirmation détaillée avant de renommer réellement les lignes visibles, cochées et valides.",
            "Afficher cochés": "Affiche ou masque les lignes cochées dans la liste.",
            "Afficher décochés": "Affiche ou masque les lignes décochées dans la liste.",
            "Tout cocher visible": "Coche toutes les lignes actuellement visibles après filtre et affichage.",
            "Tout décocher visible": "Décoche toutes les lignes actuellement visibles après filtre.",
            "Inverser visible": "Inverse la sélection cochée/décochée des lignes visibles.",
            "Log :": "Historique des chargements, filtres, renommages et erreurs.",
        }
        tips_by_variable = {
            str(self.folder_var): "Chemin du dossier de travail. Cliquez ensuite sur Charger.",
            str(self.filter_text_var): "Filtre texte non instantané : joker * possible, mais * seul est interdit. Cliquez sur Appliquer filtres.",
            str(self.filter_ext_var): "Extensions de fichiers à garder visibles. Exemples : dwg pdf d* *wg. * seul est interdit.",
            str(self.search_var): "Recherche avec joker * possible. Exemple : PLAN* ou *ancien*.",
            str(self.replace_var): "Texte de remplacement. L'aperçu montre le résultat avant action réelle.",
        }

        def walk(widget) -> None:
            text = ""
            try:
                text = str(widget.cget("text"))
            except Exception:
                pass
            if text in tips_by_text:
                Tooltip(widget, tips_by_text[text])

            try:
                var_name = str(widget.cget("textvariable"))
            except Exception:
                var_name = ""
            if var_name in tips_by_variable:
                Tooltip(widget, tips_by_variable[var_name])

            if isinstance(widget, tk.Text):
                Tooltip(widget, "Zone d'information en lecture seule ou journal selon l'onglet.")

            for child in widget.winfo_children():
                walk(child)

        walk(self.root)

    def choose_folder(self) -> None:
        folder = filedialog.askdirectory(title="Choisir le dossier")
        if folder:
            self.folder_var.set(folder)
            self.status_var.set("Dossier sélectionné. Cliquez sur Charger pour afficher le contenu.")

    def load_items(self) -> None:
        if self.loading:
            return

        folder = self.folder_var.get().strip()
        if not folder:
            messagebox.showinfo(APP_TITLE, "Choisissez d'abord un dossier.")
            return

        base = Path(folder)
        if not base.exists() or not base.is_dir():
            messagebox.showerror(APP_TITLE, "Le dossier sélectionné est invalide.")
            return

        mode = self.mode_var.get()
        recursive = self.recursive_var.get()
        self.loading = True
        self.items.clear()
        self.refresh_tree()
        self.load_button.configure(state="disabled")
        self.status_var.set("Chargement en arrière-plan...")

        worker = threading.Thread(target=self._scan_worker, args=(base, mode, recursive), daemon=True)
        worker.start()
        self.root.after(100, self._poll_load_queue)

    def _scan_worker(self, base: Path, mode: str, recursive: bool) -> None:
        try:
            paths = list(self._scan_paths(base, mode, recursive))
            self.load_queue.put(("ok", base, mode, paths, None))
        except Exception as exc:
            self.load_queue.put(("error", base, mode, [], exc))

    def _scan_paths(self, base: Path, mode: str, recursive: bool):
        if mode == "folders":
            if recursive:
                for root, dirs, _files in os.walk(base):
                    for name in dirs:
                        yield Path(root) / name
            else:
                for path in base.iterdir():
                    if path.is_dir():
                        yield path
        else:
            if recursive:
                for root, _dirs, files in os.walk(base):
                    for name in files:
                        yield Path(root) / name
            else:
                for path in base.iterdir():
                    if path.is_file():
                        yield path

    def _poll_load_queue(self) -> None:
        try:
            status, base, mode, paths, error = self.load_queue.get_nowait()
        except queue.Empty:
            self.root.after(80, self._poll_load_queue)
            return

        self.load_button.configure(state="normal")
        self.loading = False

        if status == "error":
            self.status_var.set("Erreur de chargement.")
            self.log_line(f"ERREUR chargement : {error}")
            messagebox.showerror(APP_TITLE, f"Erreur pendant le chargement :\n{error}")
            return

        self.base_dir = base
        is_dir_mode = mode == "folders"
        self.items = [RenameItem(path, base, is_dir=is_dir_mode) for path in paths]
        self.log_line(f"Chargé : {len(self.items)} élément(s) en mode {'dossiers' if is_dir_mode else 'fichiers'}.")
        self.update_preview_and_refresh()

    def apply_filters(self) -> None:
        raw_text = self.filter_text_var.get().strip()
        raw_ext = self.filter_ext_var.get().strip()

        if self._is_global_wildcard(raw_text):
            messagebox.showwarning(APP_TITLE, "Filtre texte interdit : le caractère * seul afficherait tout. Ajoutez du texte autour du joker.")
            self.log_line("WARNING : filtre texte global '*' refusé.")
            return

        if self._extension_filter_has_global_wildcard(raw_ext):
            messagebox.showwarning(APP_TITLE, "Filtre extension interdit : le caractère * seul afficherait toutes les extensions. Ajoutez du texte autour du joker.")
            self.log_line("WARNING : filtre extension global '*' refusé.")
            return

        self.applied_filter_text = raw_text.lower()
        self.applied_filter_exts = self._parse_extension_filter(raw_ext)
        self.update_preview_and_refresh()
        self.log_line("Filtres appliqués.")

    def reset_filters(self) -> None:
        self.filter_text_var.set("")
        self.filter_ext_var.set("")
        self.applied_filter_text = ""
        self.applied_filter_exts = []
        self.update_preview_and_refresh()
        self.log_line("Filtres réinitialisés.")

    def _parse_extension_filter(self, raw: str) -> list[str]:
        result: list[str] = []
        for part in re.split(r"[;,\s]+", raw.strip()):
            ext = part.strip().lower()
            if not ext:
                continue
            if ext == "sans":
                result.append("")
            else:
                result.append(ext if ext.startswith(".") else "." + ext)
        return result

    def _extension_filter_has_global_wildcard(self, raw: str) -> bool:
        return any(self._is_global_wildcard(part.strip()) for part in re.split(r"[;,\s]+", raw.strip()) if part.strip())

    def _matches_wildcard_filter(self, value: str, pattern: str) -> bool:
        if "*" not in pattern:
            return pattern in value
        regex = self._search_to_regex(pattern)
        try:
            return re.search(regex, value) is not None
        except re.error:
            return False

    def item_matches_active_filters(self, item: RenameItem) -> bool:
        if self.applied_filter_text:
            haystack = f"{item.path.name}\n{item.rel_path}".lower()
            if not self._matches_wildcard_filter(haystack, self.applied_filter_text):
                return False

        if item.is_dir and self.applied_filter_exts:
            return False
        if not item.is_dir and self.applied_filter_exts:
            if not any(self._matches_wildcard_filter(item.ext, ext_filter) for ext_filter in self.applied_filter_exts):
                return False
        return True

    def item_matches_display_filters(self, item: RenameItem) -> bool:
        if not self.item_matches_active_filters(item):
            return False
        if item.checked and not self.show_checked_var.get():
            return False
        if not item.checked and not self.show_unchecked_var.get():
            return False
        return True

    def update_preview_and_refresh(self) -> None:
        if self._is_global_wildcard(self.search_var.get()):
            messagebox.showwarning(APP_TITLE, "Recherche interdite : le caractère * seul remplacerait tout le nom. Ajoutez du texte autour du joker.")
            self.log_line("WARNING : recherche globale '*' refusée.")
            return
        self.update_preview(refresh=False)
        self.refresh_tree()

    def update_preview(self, refresh: bool = True) -> None:
        search = self.search_var.get()
        replace = self.replace_var.get()
        flags = 0 if self.case_var.get() else re.IGNORECASE

        # Recalcule uniquement les éléments réellement ciblés par l'action de renommage
        # (cochés + filtres texte/extension appliqués). Les options d'affichage
        # Afficher cochés/décochés ne doivent jamais modifier les noms enregistrés.
        for item in self.items:
            if item.checked and self.item_matches_active_filters(item) and not item.manual_name.strip():
                item.preview_name = self._preview_name(item.path.name, search, replace, flags)

        self.validate_all()
        if refresh:
            self.refresh_tree()

    def _is_global_wildcard(self, search: str) -> bool:
        return bool(search) and all(char == "*" for char in search.strip())

    def _search_to_regex(self, search: str) -> str:
        parts = [re.escape(part) for part in search.split("*")]
        return ".*".join(parts)

    def _preview_name(self, current_name: str, search: str, replace: str, flags: int) -> str:
        if not search:
            return current_name
        pattern = self._search_to_regex(search) if "*" in search else re.escape(search)
        try:
            return re.sub(pattern, replace, current_name, flags=flags)
        except re.error:
            return current_name

    def validate_name(self, name: str) -> str:
        if not name or name in (".", ".."):
            return "Nom vide/invalide"
        if any(char in WINDOWS_INVALID_CHARS for char in name):
            return "Caractère interdit Windows"
        if Path(name).stem.upper() in WINDOWS_RESERVED_NAMES:
            return "Nom réservé Windows"
        if name.endswith(" ") or name.endswith("."):
            return "Fin par espace/point interdite"
        return "OK"

    def validate_all(self) -> None:
        """Recalcule tous les statuts à partir de l'état enregistré, sans dépendre
        de l'affichage, du filtrage visible ou de la sélection dans le tableau.
        """
        statuses: dict[RenameItem, str] = {}
        targets: dict[Path, list[RenameItem]] = {}

        for item in self.items:
            target_name = item.target_name()
            status = self.validate_name(target_name)
            statuses[item] = status
            if status == "OK" and target_name != item.path.name:
                targets.setdefault(item.target_path().resolve(), []).append(item)

        for group in targets.values():
            if len(group) > 1:
                for item in group:
                    statuses[item] = "Conflit doublon"

        for item in self.items:
            if statuses[item] != "OK":
                continue
            target = item.target_path()
            if target.name == item.path.name:
                statuses[item] = "Inchangé"
            elif target.exists() and target.resolve() != item.path.resolve():
                statuses[item] = "Existe déjà"
            else:
                statuses[item] = "Renommé"

        self.item_status = statuses

    def refresh_tree(self) -> None:
        self.validate_all()
        self.tree.delete(*self.tree.get_children())
        self.iid_to_item.clear()
        self.visible_ids.clear()

        visible_items = self._sorted_items([item for item in self.items if self.item_matches_display_filters(item)])
        for row_index, item in enumerate(visible_items):
            iid = str(id(item))
            self.iid_to_item[iid] = item
            self.visible_ids.append(iid)
            tag = "even" if row_index % 2 == 0 else "odd"
            tags = (tag,)
            if self.item_status.get(item) == "Renommé":
                tags = tags + ("renamed",)
            if self.undo_is_available(item):
                tags = tags + ("undo_available",)
            self.tree.insert("", "end", iid=iid, values=self._tree_values(item), tags=tags)

        checked = sum(1 for iid in self.visible_ids if self.iid_to_item[iid].checked)
        self.status_var.set(f"Visible : {len(self.visible_ids)} | Cochés : {checked} | Total chargé : {len(self.items)}")

    def undo_is_available(self, item: RenameItem) -> bool:
        status = self.item_status.get(item, "Inchangé")
        return status in ("Renommé", "Conflit doublon") and item.target_name() != item.path.name

    def _tree_values(self, item: RenameItem) -> tuple[str, str, str, str, str, str, str, str]:
        status = self.item_status.get(item, "Inchangé")
        return (
            CHECKED if item.checked else UNCHECKED,
            item.kind,
            item.parent_folder,
            item.path.name,
            item.ext,
            item.target_name(),
            status,
            "[ ↶ ANNULER ]" if self.undo_is_available(item) else "",
        )

    def _sorted_items(self, items: list[RenameItem]) -> list[RenameItem]:
        key_functions = {
            "check": lambda item: CHECKED if item.checked else UNCHECKED,
            "kind": lambda item: item.kind.lower(),
            "parent": lambda item: item.parent_folder.lower(),
            "name": lambda item: item.path.name.lower(),
            "ext": lambda item: item.ext.lower(),
            "newname": lambda item: item.target_name().lower(),
            "status": lambda item: self.item_status.get(item, "Inchangé").lower(),
            "action": lambda item: "annuler" if self.undo_is_available(item) else "",
        }
        return sorted(items, key=key_functions.get(self.sort_column, key_functions["parent"]), reverse=self.sort_reverse)

    def sort_by_column(self, column: str) -> None:
        if self.sort_column == column:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_column = column
            self.sort_reverse = False
        self._update_sort_headers()
        self.refresh_tree()

    def _update_sort_headers(self) -> None:
        for column, title in self.column_titles.items():
            suffix = ""
            if column == self.sort_column:
                suffix = SORT_DESC if self.sort_reverse else SORT_ASC
            self.tree.heading(column, text=title + suffix, command=lambda c=column: self.sort_by_column(c))

    def on_tree_click(self, event) -> None:
        region = self.tree.identify("region", event.x, event.y)
        column = self.tree.identify_column(event.x)
        iid = self.tree.identify_row(event.y)
        if region != "cell" or iid not in self.iid_to_item:
            return

        item = self.iid_to_item[iid]
        col_index = int(column.replace("#", ""))
        col_name = self.tree["columns"][col_index - 1]

        if col_name == "check":
            item.checked = not item.checked
            self.refresh_tree()
        elif col_name == "action" and self.undo_is_available(item):
            self.undo_item_rename(item)

    def on_tree_double_click(self, event) -> str | None:
        region = self.tree.identify("region", event.x, event.y)
        column = self.tree.identify_column(event.x)
        iid = self.tree.identify_row(event.y)
        if region != "cell" or iid not in self.iid_to_item:
            return None

        col_index = int(column.replace("#", ""))
        col_name = self.tree["columns"][col_index - 1]
        if col_name == "newname":
            self.begin_inline_edit(iid)
            return "break"
        return None

    def begin_inline_edit(self, iid: str) -> None:
        if self.edit_entry is not None:
            self.finish_inline_edit(commit=True)

        bbox = self.tree.bbox(iid, "newname")
        if not bbox:
            return
        x, y, width, height = bbox
        item = self.iid_to_item[iid]
        self.editing_iid = iid
        self.edit_entry = ttk.Entry(self.tree)
        self.edit_entry.insert(0, item.target_name())
        self.edit_entry.select_range(0, "end")
        self.edit_entry.place(x=x, y=y, width=width, height=height)
        self.edit_entry.focus_set()
        self.edit_entry.bind("<Return>", lambda _event: self.finish_inline_edit(commit=True))
        self.edit_entry.bind("<KP_Enter>", lambda _event: self.finish_inline_edit(commit=True))
        self.edit_entry.bind("<Escape>", lambda _event: self.finish_inline_edit(commit=False))
        self.edit_entry.bind("<FocusOut>", lambda _event: self.finish_inline_edit(commit=True))

    def finish_inline_edit(self, commit: bool = True) -> None:
        entry = self.edit_entry
        iid = self.editing_iid
        if entry is None:
            return

        new_name = entry.get().strip()
        entry.destroy()
        self.edit_entry = None
        self.editing_iid = None

        if commit and iid in self.iid_to_item:
            item = self.iid_to_item[iid]
            item.manual_name = new_name
            if not new_name:
                item.manual_name = ""
                item.preview_name = item.path.name
            self.refresh_tree()

    def undo_item_rename(self, item: RenameItem) -> None:
        old_target = item.target_name()
        item.manual_name = ""
        item.preview_name = item.path.name
        self.log_line(f"ANNULÉ : {item.path.name} <- {old_target}")
        self.refresh_tree()

    def set_visible_checked(self, value: bool) -> None:
        for iid in self.visible_ids:
            self.iid_to_item[iid].checked = value
        self.refresh_tree()

    def invert_visible_checked(self) -> None:
        for iid in self.visible_ids:
            item = self.iid_to_item[iid]
            item.checked = not item.checked
        self.refresh_tree()

    def _relative_display(self, path: Path) -> str:
        if self.base_dir is None:
            return str(path)
        try:
            return str(path.relative_to(self.base_dir))
        except ValueError:
            return str(path)

    def confirm_rename_operations(self, operations: list[tuple[RenameItem, Path, Path, int]]) -> bool:
        count = len(operations)
        if not operations:
            return False
        item_kind = "dossier" if operations[0][0].is_dir else "fichier"
        plural = "dossiers" if operations[0][0].is_dir else "fichiers"
        label = plural if count > 1 else item_kind

        dialog = tk.Toplevel(self.root)
        dialog.title("Confirmation du renommage")
        dialog.configure(bg="#1f232a")
        dialog.geometry("980x520")
        dialog.minsize(760, 420)
        dialog.transient(self.root)
        dialog.grab_set()
        self._enable_windows_dark_titlebar_for_window(dialog)

        container = tk.Frame(dialog, bg="#1f232a", padx=14, pady=14)
        container.pack(fill="both", expand=True)

        title = f"Êtes-vous sûr de procéder au renommage de {count} {label} ?"
        tk.Label(container, text=title, bg="#1f232a", fg="#f9fafb", font=("Segoe UI", 12, "bold")).pack(anchor="w")
        tk.Label(container, text="Vérifiez la liste complète ci-dessous avant de confirmer.", bg="#1f232a", fg="#cbd5e1").pack(anchor="w", pady=(2, 10))

        columns = ("type", "actuel", "nouveau")
        preview = ttk.Treeview(container, columns=columns, show="headings")
        preview.heading("type", text="Type")
        preview.heading("actuel", text="Chemin actuel")
        preview.heading("nouveau", text="Nouveau chemin")
        preview.column("type", width=90, anchor="center", stretch=False)
        preview.column("actuel", width=410)
        preview.column("nouveau", width=410)
        preview.tag_configure("change", foreground="#f59e0b")
        preview.pack(side="left", fill="both", expand=True)

        scrollbar = ttk.Scrollbar(container, orient="vertical", command=preview.yview, style="Vertical.TScrollbar")
        preview.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")

        for item, source, destination, _depth in operations:
            preview.insert("", "end", values=(item.kind, self._relative_display(source), self._relative_display(destination)), tags=("change",))

        bottom = tk.Frame(dialog, bg="#1f232a", padx=14, pady=12)
        bottom.pack(fill="x")
        result = {"confirm": False}

        def confirm() -> None:
            result["confirm"] = True
            dialog.destroy()

        def cancel() -> None:
            dialog.destroy()

        ttk.Button(bottom, text="Annuler", command=cancel).pack(side="right", padx=(8, 0))
        ttk.Button(bottom, text=f"Oui, renommer {count} {label}", command=confirm, style="Danger.TButton").pack(side="right")
        dialog.protocol("WM_DELETE_WINDOW", cancel)
        self.root.wait_window(dialog)
        return result["confirm"]

    def rename_checked(self) -> None:
        if self.loading:
            messagebox.showinfo(APP_TITLE, "Veuillez attendre la fin du chargement.")
            return
        if self._is_global_wildcard(self.search_var.get()):
            messagebox.showwarning(APP_TITLE, "Recherche interdite : le caractère * seul remplacerait tout le nom. Ajoutez du texte autour du joker.")
            return

        self.update_preview(refresh=False)
        to_rename = [item for item in self.items if item.checked and self.item_matches_display_filters(item)]
        if not to_rename:
            messagebox.showinfo(APP_TITLE, "Aucun élément coché dans le filtre actuel.")
            return

        errors = [(item, self.item_status[item]) for item in to_rename if self.item_status[item] not in ("Renommé", "Inchangé")]
        if errors:
            message = "Corrigez d'abord les erreurs :\n" + "\n".join(f"- {item.rel_path}: {status}" for item, status in errors[:12])
            messagebox.showerror(APP_TITLE, message)
            return

        operations = [(item, item.path, item.target_path(), item.depth) for item in to_rename if item.target_path().name != item.path.name]
        if not operations:
            messagebox.showinfo(APP_TITLE, "Aucun changement à appliquer.")
            return

        if not self.confirm_rename_operations(operations):
            return

        operations.sort(key=lambda op: op[3], reverse=True)
        temp_operations: list[tuple[Path, Path, Path]] = []
        try:
            for _item, source, destination, _depth in operations:
                temporary = source.with_name(f".__renamer_tmp_{uuid.uuid4().hex}__{source.name}")
                source.rename(temporary)
                temp_operations.append((temporary, source, destination))

            for temporary, _source, destination in temp_operations:
                temporary.rename(destination)
                self.log_line(f"OK : {temporary.name} -> {destination.name}")

            messagebox.showinfo(APP_TITLE, f"Terminé : {len(operations)} élément(s) renommé(s).")
        except Exception as exc:
            self.log_line(f"ERREUR : {exc}")
            self._rollback(temp_operations)
            messagebox.showerror(APP_TITLE, f"Erreur pendant le renommage :\n{exc}")
        finally:
            self.load_items()

    def _rollback(self, temp_operations: list[tuple[Path, Path, Path]]) -> None:
        for temporary, source, _destination in reversed(temp_operations):
            try:
                if temporary.exists() and not source.exists():
                    temporary.rename(source)
            except Exception as exc:
                self.log_line(f"Rollback impossible : {exc}")

    def log_line(self, text: str) -> None:
        self.log.insert("end", text + "\n")
        self.log.see("end")


def main() -> None:
    root = tk.Tk()
    RenamerDarkUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()
