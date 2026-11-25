-- Prove2me | solution 1 for KneserColouring.IsRoom.perm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:48.760746+00:00
-- url     : https://prove2.me/submissions/55501422-afe3-4e29-95ee-1477398b5c47

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
namespace IsRoom
theorem _root_.solution {k : ℕ} {r : Room n} (h : IsRoom k r) {c : Fin n} (hc : c.val < k) :
    (r.2 c).val < k := by
  by_contra h'
  rw [not_lt] at h'
  have h2 := r.2.injective (h.2 (r.2 c) h')
  rw [h2] at h'
  omega
end IsRoom
end KneserColouring
