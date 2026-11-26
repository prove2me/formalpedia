-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.eulerDefect_merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:12.153334+00:00
-- url     : https://prove2.me/submissions/193d7568-da4c-4569-9c80-ae64400efe8d

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_right
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_of_sameCycle_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_rel_apply_of_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_not_sameCycle
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_sameCycle
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_le_of_le
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_mulSwap_of_not


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable [DecidableEq D]
variable [Finite D]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {σ α : Perm D} {x y : D} (hne : x ≠ y) (hαx : α x = y)
    (hαy : α y = x) (h : ¬ SameCycle σ x y) :
    eulerDefect (σ * swap x y) (α * swap x y) ≤ eulerDefect σ α := by
  have hc1 := cycleCount_mul_swap_of_not_sameCycle h
  have hαs : SameCycle α x y := ⟨1, by simp [hαx]⟩
  have hc2 := cycleCount_mul_swap_of_sameCycle hne hαs
  have hφ : σ * swap x y * (α * swap x y) = σ * α := by
    ext z
    simp only [Perm.mul_apply]
    by_cases hzx : z = x
    · subst hzx; simp [hαx, hαy]
    by_cases hzy : z = y
    · subst hzy; simp [hαx, hαy]
    have h1 : α z ≠ x := fun e => hzy (α.injective (e.trans hαy.symm))
    have h2 : α z ≠ y := fun e => hzx (α.injective (e.trans hαx.symm))
    rw [swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne h1 h2]
  have hxy : compSetoid (σ * swap x y) (α * swap x y) x y :=
    compSetoid_of_sameCycle_left (sameCycle_mulSwap_of_not h)
  have hK : numComponents (σ * swap x y) (α * swap x y) ≤ numComponents σ α := by
    refine numClasses_le_of_le (fun u v huv => ?_)
    exact compSetoid_le _ (rel_apply_of_mulSwap _ σ x y (compSetoid_left _ _) hxy)
      (rel_apply_of_mulSwap _ α x y (compSetoid_right _ _) hxy) huv
  unfold eulerDefect
  rw [hφ]
  omega
end LeanPool.K5MinorFreeChoosability
