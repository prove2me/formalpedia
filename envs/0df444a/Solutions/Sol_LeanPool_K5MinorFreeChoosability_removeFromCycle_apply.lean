-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.removeFromCycle_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:56.562533+00:00
-- url     : https://prove2.me/submissions/78ff63e1-3870-4a71-8bbc-ef7354ef9dcc

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (π : Perm α) {z u : α} (huz : u ≠ z) :
    removeFromCycle π z u = if π u = z then π z else π u := by
  unfold removeFromCycle
  by_cases hu : u = π⁻¹ z
  · subst hu
    simp
  · have hne : π u ≠ z := fun h => hu (by rw [← h]; simp)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hu huz]
    simp [hne]
end LeanPool.K5MinorFreeChoosability
