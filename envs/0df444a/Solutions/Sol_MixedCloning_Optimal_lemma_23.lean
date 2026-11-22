-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_23
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:28:44.541237+00:00
-- url     : https://prove2.me/submissions/6e626b26-8480-46d2-9916-e854cf4cb629
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MixedCloning_Optimal_Schur
import Theorems.Thm_MixedCloning_Optimal_hook_content

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-! Reduction of Lemma 23 (Schur ratio identities under first-row deletion)
to the hook-content formula `MixedCloning.Optimal.hook_content`. -/

/-- Cells of `tailDiagram K` are the cells of `K` below the first row, shifted up. -/
theorem l23_mem_tail (K : YoungDiagram) (y : ℕ × ℕ) :
    y ∈ tailDiagram K ↔ (y.1 + 1, y.2) ∈ K := by
  rw [← YoungDiagram.mem_cells, ← YoungDiagram.mem_cells]
  simp only [tailDiagram, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, hpos⟩, rfl⟩
    have e : ((c.1 - 1, c.2).1 + 1, (c.1 - 1, c.2).2) = c :=
      Prod.ext (by dsimp only; omega) rfl
    rw [e]; exact hc
  · intro h
    exact ⟨(y.1 + 1, y.2), ⟨h, Nat.succ_pos _⟩, Prod.ext (by dsimp only; omega) rfl⟩

theorem l23_height_le_iff (K : YoungDiagram) (t : ℕ) : height K ≤ t ↔ (t, 0) ∉ K := by
  rw [YoungDiagram.mem_iff_lt_colLen]
  exact not_lt.symm

theorem l23_height_tail (K : YoungDiagram) (t : ℕ) (ht : 1 ≤ t) (hK : height K ≤ t) :
    height (tailDiagram K) ≤ t - 1 := by
  rw [l23_height_le_iff] at hK ⊢
  rw [l23_mem_tail]
  have e : t - 1 + 1 = t := Nat.sub_add_cancel ht
  simpa only [e] using hK

theorem l23_height_sup (L M : YoungDiagram) (t : ℕ) (hL : height L ≤ t) (hM : height M ≤ t) :
    height (L ⊔ M) ≤ t := by
  rw [l23_height_le_iff] at hL hM ⊢
  rw [YoungDiagram.mem_sup]
  tauto

/-- `schurCount K t > 0` when `height K ≤ t`: fill row `i` with the letter `i`. -/
theorem l23_schurCount_pos (K : YoungDiagram) (t : ℕ) (h : height K ≤ t) :
    0 < schurCount K t := by
  unfold schurCount
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨fun c => ⟨c.val.1, ?_⟩, ?_⟩⟩
  · have h1 : c.val.1 < K.colLen c.val.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp ((YoungDiagram.mem_cells _).mp c.property)
    have h2 := K.colLen_anti 0 c.val.2 (Nat.zero_le _)
    have h3 : K.colLen 0 ≤ t := h
    omega
  · unfold IsSSYT
    refine ⟨fun a b hab _ => ?_, fun a b _ hlt => ?_⟩
    · simp only [Fin.le_def]; omega
    · simp only [Fin.lt_def]; omega

theorem l23_hook_pos (K : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ K.cells) : 0 < hook K c := by
  unfold hook
  exact Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, Or.inl ⟨rfl, le_rfl⟩⟩⟩

/-- Hooks of cells below the first row do not change when the first row is deleted. -/
theorem l23_hook_tail (K : YoungDiagram) (y : ℕ × ℕ) :
    hook (tailDiagram K) y = hook K (y.1 + 1, y.2) := by
  unfold hook
  apply Finset.card_nbij' (fun x => (x.1 + 1, x.2)) (fun x => (x.1 - 1, x.2))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells, l23_mem_tail] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells, l23_mem_tail] at hx ⊢
    have hx1 : 1 ≤ x.1 := by omega
    have e : (x.1 - 1 + 1, x.2) = x := Prod.ext (by dsimp only; omega) rfl
    rw [e]
    exact ⟨hx.1, by omega⟩
  · intro x _
    exact Prod.ext (by dsimp only; omega) rfl
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hx
    have hx1 : 1 ≤ x.1 := by omega
    exact Prod.ext (by dsimp only; omega) rfl

/-- Shifting a cell down one row lowers its content by one. -/
theorem l23_content_succ (y : ℕ × ℕ) : content (y.1 + 1, y.2) = content y - 1 := by
  unfold content
  push_cast
  ring

/-- Peeling the first row off the hook-content product. -/
theorem l23_peel (K : YoungDiagram) (t : ℕ) (ht : 1 ≤ t) (hK : height K ≤ t) :
    (schurCount K t : ℝ) =
      (∏ c ∈ K.cells.filter (fun c => c.1 = 0), ((t : ℝ) + (content c : ℝ)) / hook K c) *
        (schurCount (tailDiagram K) (t - 1) : ℝ) := by
  have hT := l23_height_tail K t ht hK
  rw [(hook_content t K hK).2, (hook_content (t - 1) (tailDiagram K) hT).2]
  rw [← Finset.prod_filter_mul_prod_filter_not K.cells (fun c => c.1 = 0)]
  congr 1
  symm
  apply Finset.prod_nbij' (fun x => (x.1 + 1, x.2)) (fun x => (x.1 - 1, x.2))
  · intro x hx
    rw [YoungDiagram.mem_cells, l23_mem_tail] at hx
    rw [Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨hx, by dsimp only; omega⟩
  · intro x hx
    rw [Finset.mem_filter, YoungDiagram.mem_cells] at hx
    rw [YoungDiagram.mem_cells, l23_mem_tail]
    have e : ((x.1 - 1, x.2).1 + 1, (x.1 - 1, x.2).2) = x :=
      Prod.ext (by dsimp only; omega) rfl
    rw [e]; exact hx.1
  · intro x _
    exact Prod.ext (by dsimp only; omega) rfl
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Prod.ext (by dsimp only; omega) rfl
  · intro x _
    rw [l23_hook_tail, l23_content_succ, Nat.cast_sub ht, Nat.cast_one]
    push_cast
    ring

/-- `tailDiagram` commutes with the union of diagrams. -/
theorem l23_tail_sup (L M : YoungDiagram) :
    tailDiagram (L ⊔ M) = tailDiagram L ⊔ tailDiagram M := by
  apply SetLike.ext
  intro y
  simp only [l23_mem_tail, YoungDiagram.mem_sup]

/-- If `μ₁ ≤ λ₁` then `λ ∪ μ` and `λ` have the same first row. -/
theorem l23_row0_sup (L M : YoungDiagram) (h : M.rowLen 0 ≤ L.rowLen 0) :
    (L ⊔ M).cells.filter (fun c => c.1 = 0) = L.cells.filter (fun c => c.1 = 0) := by
  ext c
  simp only [Finset.mem_filter, YoungDiagram.cells_sup, Finset.mem_union]
  constructor
  · rintro ⟨hc | hc, h0⟩
    · exact ⟨hc, h0⟩
    · refine ⟨?_, h0⟩
      obtain ⟨i, j⟩ := c
      dsimp only at h0
      subst h0
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
      omega
  · rintro ⟨hc, h0⟩
    exact ⟨Or.inl hc, h0⟩

theorem l23_alg1 (Fr Fd HL HN a b p q : ℝ) (hFr : Fr ≠ 0) (hFd : Fd ≠ 0) (hHL : HL ≠ 0)
    (hHN : HN ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    (Fr / HL * a) / (Fd / HL * b) * (b / a) = (Fr / HN * p) / (Fd / HN * q) * (q / p) := by
  field_simp

theorem l23_alg2 (Fr Fd HL HN a b p q : ℝ) (hFr : Fr ≠ 0) (hFd : Fd ≠ 0) (hHL : HL ≠ 0)
    (hHN : HN ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    (Fr / HN * p) / (Fd / HN * q) * ((Fd / HL * b) / b) = (p / q) * ((Fr / HL * a) / a) := by
  field_simp

theorem l23_ne_of_eq {x y : ℝ} (h : x = y) (hx : 0 < x) : y ≠ 0 := by
  rw [← h]; exact hx.ne'

theorem solution (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L M : YoungDiagram) (hL : height L ≤ r) (hM : height M ≤ r)
    (hfirst : M.rowLen 0 ≤ L.rowLen 0) :
    ratio L r d * ((schurCount (tailDiagram L) (d-1) : ℝ) / schurCount (tailDiagram L) (r-1)) =
      ratio (L ⊔ M) r d * ((schurCount (tailDiagram L ⊔ tailDiagram M) (d-1) : ℝ) /
        schurCount (tailDiagram L ⊔ tailDiagram M) (r-1)) ∧
    ratio (L ⊔ M) r d * ((schurCount L d : ℝ) / schurCount (tailDiagram L) (d-1)) =
      ratio (tailDiagram L ⊔ tailDiagram M) (r-1) (d-1) *
        ((schurCount L r : ℝ) / schurCount (tailDiagram L) (r-1)) := by
  have hN : height (L ⊔ M) ≤ r := l23_height_sup L M r hL hM
  have hLd : height L ≤ d := le_trans hL hrd
  have hNd : height (L ⊔ M) ≤ d := le_trans hN hrd
  -- positivity of the eight Schur counts
  have sLr := Nat.cast_pos (α := ℝ) |>.mpr (l23_schurCount_pos L r hL)
  have sLd := Nat.cast_pos (α := ℝ) |>.mpr (l23_schurCount_pos L d hLd)
  have sNr := Nat.cast_pos (α := ℝ) |>.mpr (l23_schurCount_pos (L ⊔ M) r hN)
  have sNd := Nat.cast_pos (α := ℝ) |>.mpr (l23_schurCount_pos (L ⊔ M) d hNd)
  have ha := (Nat.cast_pos (α := ℝ) |>.mpr
    (l23_schurCount_pos (tailDiagram L) (r - 1) (l23_height_tail L r hr hL))).ne'
  have hb := (Nat.cast_pos (α := ℝ) |>.mpr
    (l23_schurCount_pos (tailDiagram L) (d - 1) (l23_height_tail L d hd hLd))).ne'
  have hp := (Nat.cast_pos (α := ℝ) |>.mpr
    (l23_schurCount_pos (tailDiagram (L ⊔ M)) (r - 1) (l23_height_tail _ r hr hN))).ne'
  have hq := (Nat.cast_pos (α := ℝ) |>.mpr
    (l23_schurCount_pos (tailDiagram (L ⊔ M)) (d - 1) (l23_height_tail _ d hd hNd))).ne'
  -- peel the first row off each Schur count
  have pLr := l23_peel L r hr hL
  have pLd := l23_peel L d hd hLd
  have pNr := l23_peel (L ⊔ M) r hr hN
  have pNd := l23_peel (L ⊔ M) d hd hNd
  rw [l23_row0_sup L M hfirst] at pNr pNd
  rw [Finset.prod_div_distrib] at pLr pLd pNr pNd
  -- nonvanishing of the first-row factors
  obtain ⟨hFHr, -⟩ := mul_ne_zero_iff.mp (l23_ne_of_eq pLr sLr)
  obtain ⟨hFr, hHL⟩ := div_ne_zero_iff.mp hFHr
  obtain ⟨hFHd, -⟩ := mul_ne_zero_iff.mp (l23_ne_of_eq pLd sLd)
  obtain ⟨hFd, -⟩ := div_ne_zero_iff.mp hFHd
  obtain ⟨hFHNr, -⟩ := mul_ne_zero_iff.mp (l23_ne_of_eq pNr sNr)
  obtain ⟨-, hHN⟩ := div_ne_zero_iff.mp hFHNr
  rw [← l23_tail_sup]
  unfold ratio
  rw [pLr, pLd, pNr, pNd]
  exact ⟨l23_alg1 _ _ _ _ _ _ _ _ hFr hFd hHL hHN ha hb hp hq,
    l23_alg2 _ _ _ _ _ _ _ _ hFr hFd hHL hHN ha hb hp hq⟩
