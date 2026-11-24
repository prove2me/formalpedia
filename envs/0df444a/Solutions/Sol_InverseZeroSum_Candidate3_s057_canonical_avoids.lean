-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_canonical_avoids
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:20.614056+00:00
-- url     : https://prove2.me/submissions/952520df-d970-4de2-96f3-9ffa7323fef1

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_canonical_shortZero_fibre
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution (U : PosSeq 8)
    (hInj : Squarefree U) (hFree : ShortFree U) :
    AvoidsInnerJointPair (tripleRep U) := by
  classical
  intro I J hI hJ
  obtain ⟨a, hIa⟩ := s057_canonical_shortZero_fibre U hInj hFree hI
  obtain ⟨b, hJb⟩ := s057_canonical_shortZero_fibre U hInj hFree hJ
  by_cases hab : a = b
  · have hIJ : I = J := by
      rw [hIa, hJb, hab]
    simpa [innerJointSum, hIJ] using hI.2.2
  · have hEmpty : I ∩ J = ∅ := by
      ext i
      constructor
      · intro hi
        have hiI := (Finset.mem_inter.mp hi).1
        have hiJ := (Finset.mem_inter.mp hi).2
        rw [hIa] at hiI
        rw [hJb] at hiJ
        have ha : baseIndex i = a := (Finset.mem_filter.mp hiI).2
        have hb : baseIndex i = b := (Finset.mem_filter.mp hiJ).2
        exact (hab (ha.symm.trans hb)).elim
      · simp
    simp [innerJointSum, hEmpty, posSum]
end InverseZeroSum.Candidate3
