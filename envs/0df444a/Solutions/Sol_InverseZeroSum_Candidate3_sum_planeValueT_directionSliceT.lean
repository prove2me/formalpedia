-- Prove2me | solution 1 for InverseZeroSum.Candidate3.sum_planeValueT_directionSliceT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:05.751805+00:00
-- url     : https://prove2.me/submissions/409ca38b-48b3-45de-ad09-8389b80e5f6a

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
theorem _root_.solution (A : Finset F3T) (d : Fin 13)
    (c : Fin 3) :
    (∑ x ∈ directionSliceT A d c, planeValueT d x) =
      (directionSliceT A d c).card • c := by
  classical
  calc
    (∑ x ∈ directionSliceT A d c, planeValueT d x) =
        ∑ _x ∈ directionSliceT A d c, c := by
          exact Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
    _ = (directionSliceT A d c).card • c := by simp
end InverseZeroSum.Candidate3
