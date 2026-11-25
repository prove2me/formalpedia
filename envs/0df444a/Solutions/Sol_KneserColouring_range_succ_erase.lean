-- Prove2me | solution 1 for KneserColouring.range_succ_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:26.853881+00:00
-- url     : https://prove2.me/submissions/215e6f8b-91f6-41ce-aa80-732ab07ae7cd

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
theorem _root_.solution (k : ℕ) : (range (k + 1)).erase k = range k := by
  rw [range_add_one, erase_insert notMem_range_self]
end KneserColouring
