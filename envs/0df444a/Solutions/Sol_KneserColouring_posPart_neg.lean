-- Prove2me | solution 1 for KneserColouring.posPart_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:30.986209+00:00
-- url     : https://prove2.me/submissions/c59538a0-679e-462e-81f1-80c06541c6f2

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (x : Fin n → SignType) : posPart (-x) = negPart x := by
  ext i
  simp only [posPart, negPart, mem_filter, mem_univ, true_and, Pi.neg_apply]
  cases x i <;> decide
end KneserColouring
