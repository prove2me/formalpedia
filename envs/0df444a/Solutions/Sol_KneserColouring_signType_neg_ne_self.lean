-- Prove2me | solution 1 for KneserColouring.signType_neg_ne_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:47.80519+00:00
-- url     : https://prove2.me/submissions/e0ef2bd5-88ff-475f-9e66-a5dd2859d3a6

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
theorem _root_.solution {s : SignType} (h : s ≠ 0) : -s ≠ s := by
  cases s <;> first | exact absurd rfl h | decide
end KneserColouring
