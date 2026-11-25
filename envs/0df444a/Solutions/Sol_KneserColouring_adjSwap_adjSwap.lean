-- Prove2me | solution 1 for KneserColouring.adjSwap_adjSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:22.186571+00:00
-- url     : https://prove2.me/submissions/70e09a69-a82b-44f6-a49c-00399def62c1

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (j : ℕ) (c : Fin n) : adjSwap n j (adjSwap n j c) = c := by
  unfold adjSwap
  split_ifs
  · exact Equiv.swap_apply_self _ _ _
  · rfl
end KneserColouring
