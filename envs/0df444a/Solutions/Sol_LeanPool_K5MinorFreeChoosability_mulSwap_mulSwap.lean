-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.mulSwap_mulSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:16.003957+00:00
-- url     : https://prove2.me/submissions/341e3282-fb4a-47a5-bcd7-0afe9e49eec4

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
theorem _root_.solution (π : Perm α) (x y : α) : π * swap x y * swap x y = π := by
  rw [mul_assoc, swap_mul_self, mul_one]
end LeanPool.K5MinorFreeChoosability
