-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cycleCount_mul_swap_of_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:28.514455+00:00
-- url     : https://prove2.me/submissions/0f1418c9-a0e9-4bbc-ae8b-bec939b93358

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_congr
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_addPair_of_not
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_le_addPair_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_sameCycle_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_not_sameCycle_mulSwap_of_sameCycle

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite α] {π : Perm α} {x y : α} (hne : x ≠ y)
    (h : SameCycle π x y) : cycleCount (π * swap x y) = cycleCount π + 1 := by
  have hn := not_sameCycle_mulSwap_of_sameCycle hne h
  have hiff : ∀ a b, SameCycle.setoid π a b ↔
      addPairSetoid (SameCycle.setoid (π * swap x y)) x y a b := by
    intro a b
    refine ⟨sameCycle_le_addPair_mulSwap π x y, ?_⟩
    rintro (k | ⟨k1, k2⟩ | ⟨k1, k2⟩)
    · exact sameCycle_of_sameCycle_mulSwap h k
    · exact ((sameCycle_of_sameCycle_mulSwap h k1).trans h).trans
        (sameCycle_of_sameCycle_mulSwap h k2)
    · exact ((sameCycle_of_sameCycle_mulSwap h k1).trans h.symm).trans
        (sameCycle_of_sameCycle_mulSwap h k2)
  unfold cycleCount
  rw [numClasses_congr hiff,
    numClasses_addPair_of_not (s := SameCycle.setoid (π * swap x y)) hn]
end LeanPool.K5MinorFreeChoosability
