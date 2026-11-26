-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cycleCount_mul_swap_of_not_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:36.024503+00:00
-- url     : https://prove2.me/submissions/749fadad-a0b0-4b87-ae75-098b51f82fe4

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_congr
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_addPair_of_not
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_le_addPair_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_sameCycle_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_mulSwap_mulSwap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_mulSwap_of_not

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite α] {π : Perm α} {x y : α}
    (h : ¬ SameCycle π x y) : cycleCount (π * swap x y) + 1 = cycleCount π := by
  have hs := sameCycle_mulSwap_of_not h
  have hle : ∀ {a b}, SameCycle π a b → SameCycle (π * swap x y) a b := by
    intro a b k
    have k' : SameCycle (π * swap x y * swap x y) a b := by rwa [mulSwap_mulSwap]
    exact sameCycle_of_sameCycle_mulSwap hs k'
  have hiff : ∀ a b, SameCycle.setoid (π * swap x y) a b ↔
      addPairSetoid (SameCycle.setoid π) x y a b := by
    intro a b
    constructor
    · intro k
      have := sameCycle_le_addPair_mulSwap (π * swap x y) x y k
      rwa [mulSwap_mulSwap] at this
    · rintro (k | ⟨k1, k2⟩ | ⟨k1, k2⟩)
      · exact hle k
      · exact ((hle k1).trans hs).trans (hle k2)
      · exact ((hle k1).trans hs.symm).trans (hle k2)
  unfold cycleCount
  rw [numClasses_congr hiff, numClasses_addPair_of_not (s := SameCycle.setoid π) h]
end LeanPool.K5MinorFreeChoosability
