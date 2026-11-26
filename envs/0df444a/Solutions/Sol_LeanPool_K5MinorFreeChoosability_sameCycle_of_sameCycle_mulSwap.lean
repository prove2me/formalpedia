-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_of_sameCycle_mulSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:22.77642+00:00
-- url     : https://prove2.me/submissions/78c5bedd-8115-4c85-bf68-530b8fb26d85

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {π : Perm α} {x y : α} (hxy : SameCycle π x y)
    {a b : α} (h : SameCycle (π * swap x y) a b) : SameCycle π a b := by
  refine sameCycle_of_step (SameCycle.setoid π) (fun z => ?_) h
  change SameCycle π z ((π * swap x y) z)
  by_cases hzx : z = x
  · subst hzx
    simp only [Perm.mul_apply, swap_apply_left]
    exact hxy.trans ((sameCycle_apply_right).2 (SameCycle.refl _ _))
  by_cases hzy : z = y
  · subst hzy
    simp only [Perm.mul_apply, swap_apply_right]
    exact hxy.symm.trans ((sameCycle_apply_right).2 (SameCycle.refl _ _))
  · simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy]
    exact (sameCycle_apply_right).2 (SameCycle.refl _ _)
end LeanPool.K5MinorFreeChoosability
