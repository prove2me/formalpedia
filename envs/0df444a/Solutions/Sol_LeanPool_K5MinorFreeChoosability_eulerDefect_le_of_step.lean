-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.eulerDefect_le_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:18.981668+00:00
-- url     : https://prove2.me/submissions/f8cbc3f0-2a37-43d2-80f8-f63f54d8c763

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_of_sameCycle_mul
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_not_sameCycle
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_sameCycle
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_le_addPair_succ
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
theorem _root_.solution {σ α σ' α' : Perm D} {a b x y : D} (hab : a ≠ b)
    (hc : cycleCount σ' + cycleCount α' = cycleCount σ + cycleCount α + 1)
    (hφ : σ' * α' = σ * α * swap a b)
    (hK1 : ∀ u v, compSetoid σ α u v → addPairSetoid (compSetoid σ' α') x y u v)
    (hK2 : compSetoid σ' α' a b → ∀ u v, compSetoid σ α u v → compSetoid σ' α' u v) :
    eulerDefect σ' α' ≤ eulerDefect σ α := by
  have hK : numComponents σ' α' ≤ numComponents σ α + 1 := by
    have h1 := numClasses_le_addPair_succ (compSetoid σ' α') x y
    have h2 := numClasses_le_of_le hK1
    unfold numComponents
    omega
  unfold eulerDefect
  by_cases hs : SameCycle (σ * α) a b
  · have h1 := cycleCount_mul_swap_of_sameCycle hab hs
    rw [hφ, h1]
    push_cast
    omega
  · have h1 := cycleCount_mul_swap_of_not_sameCycle hs
    have hs' : SameCycle (σ' * α') a b := hφ ▸ sameCycle_mulSwap_of_not hs
    have hK' : numComponents σ' α' ≤ numComponents σ α :=
      numClasses_le_of_le (hK2 (compSetoid_of_sameCycle_mul hs'))
    rw [hφ]
    omega
end LeanPool.K5MinorFreeChoosability
