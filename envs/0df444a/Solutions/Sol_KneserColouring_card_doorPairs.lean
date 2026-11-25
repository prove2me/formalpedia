-- Prove2me | solution 1 for KneserColouring.card_doorPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:49.626048+00:00
-- url     : https://prove2.me/submissions/437daf2d-2d13-4136-a47e-be5d4752cd5c

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) (K : ℕ) :
    (doorPairs lab K).card =
      ∑ r ∈ univ.filter (fun r : Room n => IsUpper K r),
        ((range K).filter (door lab K r)).card := by
  rw [doorPairs, card_filter, sum_product]
  apply sum_congr rfl
  intro r _
  rw [card_filter]
end KneserColouring
