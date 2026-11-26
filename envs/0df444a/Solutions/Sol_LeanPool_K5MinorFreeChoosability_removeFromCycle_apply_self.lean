-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.removeFromCycle_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:35.999802+00:00
-- url     : https://prove2.me/submissions/28354dc1-3b0b-45b3-95c2-ec8585a171f2

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
theorem _root_.solution (π : Perm α) (z : α) : removeFromCycle π z z = z := by
  simp [removeFromCycle]
end LeanPool.K5MinorFreeChoosability
