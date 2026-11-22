-- Prove2me | solution 1 for LatinQuarter.isLatin_of_columnSymbol_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:31.261872+00:00
-- url     : https://prove2.me/submissions/62373cfe-5a39-4a93-af97-443857411af8

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {n : ℕ} {M : Square n}
    (hr : ∀ r, Function.Bijective (M r)) (hi : Function.Injective (columnSymbol M)) :
    IsLatin M := by
  refine ⟨hr, fun c => Function.Injective.bijective_of_finite ?_⟩
  intro r s h
  have he : columnSymbol M (r, c) = columnSymbol M (s, c) := Prod.ext rfl h
  exact congrArg Prod.fst (hi he)
end LatinQuarter
