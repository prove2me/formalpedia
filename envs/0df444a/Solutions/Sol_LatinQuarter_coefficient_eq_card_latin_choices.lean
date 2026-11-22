-- Prove2me | solution 1 for LatinQuarter.coefficient_eq_card_latin_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:53.907564+00:00
-- url     : https://prove2.me/submissions/8c6abc16-563b-4976-950e-f2e7dff85755

module
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Theorems.Thm_LatinQuarter_coefficient_eq_sum_latin_choices


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
      ((Finset.univ.filter
        (fun σ : RowChoices P => IsLatin (chosenSquare P L σ))).card : ZMod 2) := by
  rw [coefficient_eq_sum_latin_choices P L hL a, Finset.sum_boole]
end LatinQuarter
