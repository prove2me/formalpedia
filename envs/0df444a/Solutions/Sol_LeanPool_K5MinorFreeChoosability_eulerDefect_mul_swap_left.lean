-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.eulerDefect_mul_swap_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:37.134597+00:00
-- url     : https://prove2.me/submissions/58fd11c8-f0be-40e1-afee-5826f5f3c6db

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_right
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_addPair_apply_of_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_rel_apply_of_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_le_of_step
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_sameCycle


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable [DecidableEq D]
variable [Finite D]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {σ α : Perm D} {x y : D} (hne : x ≠ y)
    (h : SameCycle σ x y) : eulerDefect (σ * swap x y) α ≤ eulerDefect σ α := by
  have hab : α⁻¹ x ≠ α⁻¹ y := fun e => hne (by simpa using congrArg α e)
  refine eulerDefect_le_of_step (a := α⁻¹ x) (b := α⁻¹ y) (x := x) (y := y) hab ?_ ?_ ?_ ?_
  · rw [cycleCount_mul_swap_of_sameCycle hne h]
    ring
  · rw [swap_apply_apply, inv_inv]
    group
  · intro u v huv
    exact compSetoid_le _ (addPair_apply_of_mulSwap _ σ x y (compSetoid_left _ _))
      (fun z => Or.inl (compSetoid_right _ _ z)) huv
  · intro hab' u v huv
    have hxy : compSetoid (σ * swap x y) α x y := by
      have h1 := compSetoid_right (σ * swap x y) α (α⁻¹ x)
      have h2 := compSetoid_right (σ * swap x y) α (α⁻¹ y)
      rw [show α (α⁻¹ x) = x by simp] at h1
      rw [show α (α⁻¹ y) = y by simp] at h2
      exact (compSetoid _ _).trans ((compSetoid _ _).trans ((compSetoid _ _).symm h1) hab') h2
    exact compSetoid_le _ (rel_apply_of_mulSwap _ σ x y (compSetoid_left _ _) hxy)
      (compSetoid_right _ _) huv
end LeanPool.K5MinorFreeChoosability
