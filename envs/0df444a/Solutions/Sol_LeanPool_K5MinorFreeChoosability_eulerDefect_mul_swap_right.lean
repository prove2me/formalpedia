-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.eulerDefect_mul_swap_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:36.700359+00:00
-- url     : https://prove2.me/submissions/98259ebc-b3a4-4446-8e86-35dd6cdd5f3a

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
    (h : SameCycle α x y) : eulerDefect σ (α * swap x y) ≤ eulerDefect σ α := by
  refine eulerDefect_le_of_step (a := x) (b := y) (x := x) (y := y) hne ?_ (mul_assoc _ _ _)
    ?_ ?_
  · rw [cycleCount_mul_swap_of_sameCycle hne h]
    ring
  · intro u v huv
    exact compSetoid_le _ (fun z => Or.inl (compSetoid_left _ _ z))
      (addPair_apply_of_mulSwap _ α x y (compSetoid_right _ _)) huv
  · intro hxy u v huv
    exact compSetoid_le _ (compSetoid_left _ _)
      (rel_apply_of_mulSwap _ α x y (compSetoid_right _ _) hxy) huv
end LeanPool.K5MinorFreeChoosability
