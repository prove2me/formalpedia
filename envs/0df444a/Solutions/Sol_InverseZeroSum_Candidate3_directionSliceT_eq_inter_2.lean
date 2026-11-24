-- Prove2me | solution 2 for InverseZeroSum.Candidate3.directionSliceT_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:20.385104+00:00
-- url     : https://prove2.me/submissions/9f420eca-836a-4397-8ee1-114813ba420a

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
namespace InverseZeroSum.Candidate3
theorem _root_.solution (A : Finset F3T) (d : Fin 13) (c : Fin 3) :
    directionSliceT A d c = A ∩ planeSetT (d, c) := by
  classical
  ext x
  simp [directionSliceT, planeSetT, onPlaneTB]
end InverseZeroSum.Candidate3
