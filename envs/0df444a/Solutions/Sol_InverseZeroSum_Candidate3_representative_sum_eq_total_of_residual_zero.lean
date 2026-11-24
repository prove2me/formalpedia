-- Prove2me | solution 1 for InverseZeroSum.Candidate3.representative_sum_eq_total_of_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:09.593838+00:00
-- url     : https://prove2.me/submissions/5aa899a1-77c6-409a-af9f-c521fbf6f29f

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_posSum_representativeSet_eq_sum
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {s : ℕ}
    (S : PosSeq 24) {blocks : Fin s → Finset (Fin 24)}
    {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j)
    (hResidualZero :
      posSum S (Finset.univ \ representativeSet rep) = 0) :
    (∑ j : Fin s, (S (rep j) : G)) = totalSum S := by
  have hSplit :
      posSum S (representativeSet rep) +
        posSum S (Finset.univ \ representativeSet rep) =
        totalSum S := by
    simpa [posSum, totalSum, add_comm] using
      (Finset.sum_sdiff (Finset.subset_univ (representativeSet rep))
        (f := fun i => (S i : G)))
  rw [hResidualZero, add_zero] at hSplit
  rw [posSum_representativeSet_eq_sum S hBlocks hRep] at hSplit
  exact hSplit
end InverseZeroSum.Candidate3
