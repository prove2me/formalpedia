-- Prove2me | solution 1 for LatinQuarter.coefficient_eq_sum_latin_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:05.345782+00:00
-- url     : https://prove2.me/submissions/a1dc93c7-5cc1-45ed-8776-54c291e0df3a

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Theorems.Thm_LatinQuarter_expand_row_matchings
public import Theorems.Thm_LatinQuarter_full_coefficient
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_chosenSquare_rows
public import Theorems.Thm_LatinQuarter_coeff_prod_add_constants
public import Theorems.Thm_LatinQuarter_mem_completions
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
open Classical
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) =
      ∑ σ : RowChoices P, if IsLatin (chosenSquare P L σ) then (1 : ZMod 2) else 0 := by
  classical
  rw [expand_row_matchings, coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change (∏ p : Cell n, (X (columnSymbol (chosenSquare P L σ) p) +
    C (a (columnSymbol (chosenSquare P L σ) p)))).coeff (allTagsExponent (Cell n)) = _
  rw [coeff_prod_add_constants _ _ _ (by simp)]
  exact full_coefficient _ (chosenSquare_rows P L hL σ)
end LatinQuarter
