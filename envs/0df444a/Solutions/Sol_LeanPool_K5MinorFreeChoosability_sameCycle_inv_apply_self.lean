-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_inv_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:04.817217+00:00
-- url     : https://prove2.me/submissions/132a29da-33a4-4660-8ed1-4b3b27a387c7

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
omit [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (π : Perm α) (z : α) : SameCycle π (π⁻¹ z) z :=
  ⟨1, by simp⟩
end LeanPool.K5MinorFreeChoosability
