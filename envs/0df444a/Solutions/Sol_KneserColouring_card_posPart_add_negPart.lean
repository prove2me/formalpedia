-- Prove2me | solution 1 for KneserColouring.card_posPart_add_negPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:08.897624+00:00
-- url     : https://prove2.me/submissions/b4e3e48b-f252-4516-9def-654f9a50e5b1

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_disjoint_posPart_negPart

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (x : Fin n → SignType) :
    (posPart x).card + (negPart x).card = suppCard x := by
  rw [← card_union_of_disjoint (disjoint_posPart_negPart x), suppCard]
  congr 1
  ext i
  simp only [posPart, negPart, mem_union, mem_filter, mem_univ, true_and]
  cases x i <;> decide
end KneserColouring
