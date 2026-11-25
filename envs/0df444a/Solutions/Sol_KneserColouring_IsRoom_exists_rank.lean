-- Prove2me | solution 1 for KneserColouring.IsRoom.exists_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:35.9606+00:00
-- url     : https://prove2.me/submissions/9bda6fcf-2cd7-445b-a6ac-d43621e858b0

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
theorem _root_.solution {k : ℕ} {r : Room n} (h : IsRoom k r) (hk : k ≤ n) {i : ℕ}
    (hi : i < k) : ∃ c : Fin n, c.val < k ∧ (r.2 c).val = i := by
  refine ⟨r.2.symm ⟨i, by omega⟩, ?_, by simp⟩
  by_contra h'
  rw [not_lt] at h'
  have h2 := h.2 _ h'
  rw [Equiv.apply_symm_apply] at h2
  rw [← h2] at h'
  simp at h'
  omega
end IsRoom
end KneserColouring
