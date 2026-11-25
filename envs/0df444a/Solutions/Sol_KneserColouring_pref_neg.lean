-- Prove2me | solution 1 for KneserColouring.pref_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:04.14583+00:00
-- url     : https://prove2.me/submissions/c8c37d87-f784-4c57-a0c0-5528dfa76718

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
theorem _root_.solution (r : Room n) (i : ℕ) : pref (-r.1, r.2) i = -pref r i := by
  funext c
  simp only [pref, Pi.neg_apply]
  split_ifs <;> simp
end KneserColouring
