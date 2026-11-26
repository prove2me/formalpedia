-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_le_addPair_mulSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:13.313615+00:00
-- url     : https://prove2.me/submissions/2295e35a-eec9-42b6-9958-6d5837edab3b

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
theorem _root_.solution (π : Perm α) (x y : α) {a b : α}
    (h : SameCycle π a b) : addPairSetoid (SameCycle.setoid (π * swap x y)) x y a b := by
  refine sameCycle_of_step _ (fun z => ?_) h
  by_cases hzx : z = x
  · subst hzx
    refine Or.inr (Or.inl ⟨SameCycle.refl _ _, ?_⟩)
    have : π z = (π * swap z y) y := by simp
    rw [this]
    exact (sameCycle_apply_right).2 (SameCycle.refl _ _)
  by_cases hzy : z = y
  · subst hzy
    refine Or.inr (Or.inr ⟨SameCycle.refl _ _, ?_⟩)
    have : π z = (π * swap x z) x := by simp
    rw [this]
    exact (sameCycle_apply_right).2 (SameCycle.refl _ _)
  · refine Or.inl ?_
    have : π z = (π * swap x y) z := by simp [swap_apply_of_ne_of_ne hzx hzy]
    rw [this]
    exact (sameCycle_apply_right).2 (SameCycle.refl _ _)
end LeanPool.K5MinorFreeChoosability
