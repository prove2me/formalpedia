-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.removeFromCycle_eq_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:54.778246+00:00
-- url     : https://prove2.me/submissions/ee84cc53-032e-4dde-9000-8dec455cb5cf

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
theorem _root_.solution {π : Perm α} {z : α} (hz : π⁻¹ z = z) :
    removeFromCycle π z = π := by
  rw [removeFromCycle, hz, swap_self]
  exact mul_one π
end LeanPool.K5MinorFreeChoosability
