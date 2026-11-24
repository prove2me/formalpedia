-- Prove2me | solution 2 for InverseZeroSum.Candidate3.horizontalSliceT_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:19.302988+00:00
-- url     : https://prove2.me/submissions/2f276222-1464-46db-a38a-a9a30b6e3a44

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_on_horizontalPlaneT_iff
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (A : Finset F3T) (c : Fin 3) :
    horizontalSliceT A c = A ∩ planeSetT (horizontalPlaneT c) := by
  classical
  ext x
  simp [horizontalSliceT, planeSetT, on_horizontalPlaneT_iff]
end InverseZeroSum.Candidate3
