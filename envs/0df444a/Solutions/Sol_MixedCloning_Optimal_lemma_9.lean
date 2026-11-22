-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:38:59.832288+00:00
-- url     : https://prove2.me/submissions/7ce87e37-f1f6-48c4-b3e4-e38961c6b8ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MixedCloning_Optimal_Schur
import Theorems.Thm_MixedCloning_Optimal_hook_content

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

namespace L9F

/-! ### The content factor `x ↦ (r+x)/(d+x)` -/

lemma cfrac_nonneg {r d x : ℝ} (hrd : r ≤ d) (hx : 0 < r + x) : 0 ≤ (r + x) / (d + x) :=
  div_nonneg hx.le (by linarith)

lemma cfrac_le_one {r d x : ℝ} (hrd : r ≤ d) (hx : 0 < r + x) : (r + x) / (d + x) ≤ 1 := by
  rw [div_le_one (by linarith)]; linarith

lemma content_cast (c : ℕ × ℕ) : (content c : ℝ) = (c.2 : ℝ) - c.1 := by
  simp [content]

lemma content_pos_of_row {t : ℕ} (c : ℕ × ℕ) (hc : c.1 < t) : 0 < (t : ℝ) + (content c : ℝ) := by
  rw [content_cast]
  have h1 : (c.1 : ℝ) < t := by exact_mod_cast hc
  have h2 : (0 : ℝ) ≤ c.2 := Nat.cast_nonneg _
  linarith

lemma row_lt_height (A : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ A.cells) : c.1 < height A := by
  obtain ⟨i, j⟩ := c
  have : (i, 0) ∈ A := A.up_left_mem le_rfl (Nat.zero_le j) hc
  exact YoungDiagram.mem_iff_lt_colLen.mp this

/-! ### Zero count for too-tall diagrams -/

lemma card_zero_of_isEmpty {α : Type*} (inst : Fintype α) (h : IsEmpty α) :
    @Fintype.card α inst = 0 :=
  @Fintype.card_eq_zero α inst h

lemma schurCount_eq_zero (L : YoungDiagram) (t : ℕ) (h : t < height L) : schurCount L t = 0 := by
  unfold schurCount
  refine card_zero_of_isEmpty _ ⟨fun ⟨T, hT⟩ => ?_⟩
  have hmem : ∀ i, i ≤ t → (i, 0) ∈ L.cells := fun i hi =>
    YoungDiagram.mem_iff_lt_colLen.mpr (by unfold height at h; omega)
  let g : Fin (t+1) → Fin t := fun i => T ⟨(i.val, 0), hmem i.val (by omega)⟩
  have hg : StrictMono g := by
    intro a b hab
    exact hT.2 _ _ rfl hab
  have := Fintype.card_le_of_injective g hg.injective
  simp at this

lemma ratio_eq_zero (L : YoungDiagram) (t d : ℕ) (h : t < height L) : ratio L t d = 0 := by
  unfold ratio
  rw [schurCount_eq_zero L t h]
  simp

lemma ratio_nonneg (L : YoungDiagram) (t d : ℕ) : 0 ≤ ratio L t d :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### Ratios as content products (hook lengths cancel) -/

lemma hook_ne_zero (L : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ L.cells) : hook L c ≠ 0 := by
  unfold hook
  exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨hc, Or.inl ⟨rfl, le_rfl⟩⟩)

lemma ratio_eq_prod (L : YoungDiagram) (t d : ℕ) (ht : height L ≤ t) (htd : t ≤ d) :
    ratio L t d = ∏ c ∈ L.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) := by
  have h1 := (MixedCloning.Optimal.hook_content t L ht).2
  have h2 := (MixedCloning.Optimal.hook_content d L (ht.trans htd)).2
  unfold ratio
  rw [h1, h2, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun c hc => ?_
  have hh : (hook L c : ℝ) ≠ 0 := by exact_mod_cast hook_ne_zero L c hc
  exact div_div_div_cancel_right₀ hh _ _

/-! ### Monotonicity under inclusion -/

lemma height_mono (S T : YoungDiagram) (hST : S ≤ T) : height S ≤ height T := by
  unfold height
  by_contra h
  push_neg at h
  have h1 : (T.colLen 0, 0) ∈ S := YoungDiagram.mem_iff_lt_colLen.mpr h
  have h2 : (T.colLen 0, 0) ∈ T := hST h1
  have := YoungDiagram.mem_iff_lt_colLen.mp h2
  omega

lemma prod_mono_core (t d : ℕ) (htd : t ≤ d) (S T : YoungDiagram) (hST : S ≤ T)
    (hT : height T ≤ t) :
    ∏ c ∈ T.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) ≤
      ∏ c ∈ S.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) := by
  have htd' : (t : ℝ) ≤ d := by exact_mod_cast htd
  have hsub : S.cells ⊆ T.cells := YoungDiagram.cells_subset_iff.mpr hST
  have hrowT : ∀ c ∈ T.cells, c.1 < t := fun c hc => (row_lt_height T c hc).trans_le hT
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ c ∈ T.cells \ S.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) ≤ 1 :=
    Finset.prod_le_one (fun c hc => cfrac_nonneg htd'
        (content_pos_of_row c (hrowT c (Finset.mem_sdiff.mp hc).1)))
      (fun c hc => cfrac_le_one htd'
        (content_pos_of_row c (hrowT c (Finset.mem_sdiff.mp hc).1)))
  have h0 : 0 ≤ ∏ c ∈ S.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) :=
    Finset.prod_nonneg fun c hc => cfrac_nonneg htd' (content_pos_of_row c (hrowT c (hsub hc)))
  calc (∏ c ∈ T.cells \ S.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c)) *
        ∏ c ∈ S.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c)
      ≤ 1 * ∏ c ∈ S.cells, ((t : ℝ) + content c) / ((d : ℝ) + content c) :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = _ := one_mul _

end L9F

open L9F

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (d t : ℕ) (ht : 1 ≤ t) (htd : t ≤ d)
    (S T : YoungDiagram) (hS : height S ≤ d) (hT : height T ≤ d) (hST : S ≤ T) :
    ratio T t d ≤ ratio S t d := by
  by_cases hh : height T ≤ t
  · have hS' : height S ≤ t := (height_mono S T hST).trans hh
    rw [ratio_eq_prod T t d hh htd, ratio_eq_prod S t d hS' htd]
    exact prod_mono_core t d htd S T hST hh
  · push_neg at hh
    rw [ratio_eq_zero T t d hh]
    exact ratio_nonneg S t d
