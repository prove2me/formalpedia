-- Prove2me | solution 2 for InverseZeroSum.Candidate3.planeSetT_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:00.137068+00:00
-- url     : https://prove2.me/submissions/97ba2091-574d-4b82-8da5-77bb34402120

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planePointT_injective
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_eq_image
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (p : PlaneIdx) :
    (planeSetT p).card = 9 := by
  classical
  rw [planeSetT_eq_image p]
  simpa using
    Finset.card_image_of_injective (Finset.univ : Finset PlaneCoord)
      (planePointT_injective p)
end InverseZeroSum.Candidate3
