-- Prove2me | solution 1 for KneserColouring.negPart_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:50.080055+00:00
-- url     : https://prove2.me/submissions/dcf7e0b6-c65c-4ea1-aa81-c02c4e2ba57f

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
theorem _root_.solution (x : Fin n → SignType) : negPart (-x) = posPart x := by
  ext i
  simp only [posPart, negPart, mem_filter, mem_univ, true_and, Pi.neg_apply]
  cases x i <;> decide
end KneserColouring
