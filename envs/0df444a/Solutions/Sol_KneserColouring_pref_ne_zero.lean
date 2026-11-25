-- Prove2me | solution 1 for KneserColouring.pref_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:20.888804+00:00
-- url     : https://prove2.me/submissions/5406fb89-9d33-42d2-b501-aebfd50b53d1

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Theorems.Thm_KneserColouring_IsRoom_exists_rank

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {k : ℕ} {r : Room n} (h : IsRoom k r) (hk : k ≤ n) {i : ℕ} (hi : i < k) :
    pref r (i + 1) ≠ 0 := by
  obtain ⟨c, hc, hrc⟩ := h.exists_rank hk hi
  intro h0
  have h1 := congrFun h0 c
  simp only [pref, Pi.zero_apply] at h1
  rw [if_pos (by omega)] at h1
  exact (h.1 c).2 hc h1
end KneserColouring
