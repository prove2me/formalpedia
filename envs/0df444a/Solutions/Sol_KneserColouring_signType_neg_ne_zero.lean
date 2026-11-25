-- Prove2me | solution 1 for KneserColouring.signType_neg_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:16.161408+00:00
-- url     : https://prove2.me/submissions/9ee1a59d-a0e4-49c6-b33b-a5c045c1671d

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
theorem _root_.solution (s : SignType) : -s ≠ 0 ↔ s ≠ 0 := by
  cases s <;> decide
end KneserColouring
