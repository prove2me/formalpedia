-- Prove2me | solution 1 for InverseZeroSum.Candidate3.complement_insert_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:23.688952+00:00
-- url     : https://prove2.me/submissions/faca7b5f-ff89-4473-a5e4-90fb51b92619

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) {x y : α} (hx : x ∉ B) (hxy : x ≠ y) :
    (Finset.univ \ insert y B) =
      insert x ((Finset.univ \ insert x B).erase y) := by
  classical
  ext z
  by_cases hzx : z = x
  · subst z
    simp [hx, hxy]
  · by_cases hzy : z = y
    · subst z
      simp [hxy, hzx]
    · simp [hzx, hzy]
end InverseZeroSum.Candidate3
