-- Prove2me | solution 1 for LatinQuarter.small_clue_coefficient_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:50.791226+00:00
-- url     : https://prove2.me/submissions/a072f368-0bb6-42b5-b5a6-a8e8d0594249

module
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
public import Definitions.Def_LeanPool_LatinQuarter_Budget
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_clue_budget
public import Theorems.Thm_LatinQuarter_mem_completions
public import Theorems.Thm_LatinQuarter_shifted_tags_product_vanishes
public import Theorems.Thm_LatinQuarter_squarefree_coeff_zero_of_quotient_zero
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_one
attribute [local simp] LatinQuarter.mem_completions
attribute [local simp] LatinQuarter.tag_sq



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n) (hP : P.card < n * n / 4) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (markedConstant e c s)) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (markedConstant e c s))).coeff
      (allTagsExponent (Cell n)) = 0 := by
  classical
  let Y : Matrix (Fin n) (Fin n) (MvPolynomial (Cell n) (ZMod 2)) :=
    fun c s => X (c, s) + C (markedConstant e c s)
  let q := Ideal.Quotient.mk (repeatedTagIdeal (Cell n))
  have hrow : q (rowMinorProduct P L Y) = rowMinorProduct P L (shiftedTags e) := by
    unfold rowMinorProduct
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r _
    rw [q.map_det]
    congr 1
  have hz : rowMinorProduct P L (shiftedTags e) = 0 :=
    shifted_tags_product_vanishes e (fun r => FreeColumn P r)
      (fun _ c => c.val) (fun r c => L r c) (clue_budget P hP)
  have hzq : q (clueProduct P L Y * rowMinorProduct P L Y) = 0 := by
    rw [map_mul, hrow, hz, mul_zero]
  exact squarefree_coeff_zero_of_quotient_zero hzq (by simp)
end LatinQuarter
