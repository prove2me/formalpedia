-- Prove2me | solution 1 for KneserColouring.maxCol_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:09.286456+00:00
-- url     : https://prove2.me/submissions/ff0b6052-6255-41a8-bf86-2d21e31675fd

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
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) (B : Finset (Fin n)) :
    maxCol c B ≤ q := by
  apply Finset.sup_le
  intro A _
  unfold setCol
  split_ifs
  · exact (c _).isLt
  · exact Nat.zero_le _
end KneserColouring
