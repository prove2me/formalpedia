-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_removeFromCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:04.901677+00:00
-- url     : https://prove2.me/submissions/d278bbbd-fb4f-448c-8e96-e8ab06a99017

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_le_addPair_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply_self

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {π : Perm α} {z u v : α} (hu : u ≠ z)
    (hv : v ≠ z) (h : SameCycle π u v) : SameCycle (removeFromCycle π z) u v := by
  have h' := sameCycle_le_addPair_mulSwap π (π⁻¹ z) z h
  have hfix : ∀ w, SameCycle (removeFromCycle π z) z w → w = z := fun w hw =>
    (hw.eq_of_left (removeFromCycle_apply_self π z)).symm
  rcases h' with k | ⟨_, k2⟩ | ⟨k1, _⟩
  · exact k
  · exact absurd (hfix v k2) hv
  · exact absurd (hfix u k1.symm) hu
end LeanPool.K5MinorFreeChoosability
