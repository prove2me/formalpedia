-- Prove2me | solution 1 for LatinQuarter.defining_coefficient_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:53.453837+00:00
-- url     : https://prove2.me/submissions/a03220d9-517e-4927-bfed-507befcbf559

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Theorems.Thm_LatinQuarter_coefficient_eq_sum_latin_choices
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_mem_completions
public import Theorems.Thm_LatinQuarter_tag_sq
public import Theorems.Thm_LatinQuarter_unique_chosenSquare
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
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) = 1 := by
  classical
  rw [coefficient_eq_sum_latin_choices P L h.1 a]
  rw [Finset.sum_eq_single (1 : RowChoices P)]
  · simp [h.1]
  · intro σ _ hσ
    rw [if_neg]
    exact fun hl => hσ (unique_chosenSquare P L h σ hl)
  · simp
end LatinQuarter
