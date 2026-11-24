-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeValueT_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:06.320263+00:00
-- url     : https://prove2.me/submissions/38fe4543-f80a-4922-968c-e8d52f265ee4

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_add
public import Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_zero
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (d : Fin 13) (A : Finset F3T) :
    planeValueT d (∑ x ∈ A, x) = ∑ x ∈ A, planeValueT d x := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simpa using planeValueT_zero d
  | @insert a s ha ih =>
      simp [ha, planeValueT_add, ih]
end InverseZeroSum.Candidate3
