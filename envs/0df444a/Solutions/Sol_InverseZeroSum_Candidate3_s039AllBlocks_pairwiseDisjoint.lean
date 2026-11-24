-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s039AllBlocks_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:11.447802+00:00
-- url     : https://prove2.me/submissions/fc30448d-7a22-490d-aca5-b5da92d9ada2

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_disjoint_of_ne
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {S : PosSeq 24}
    (hAvoid : AvoidsInnerJointPair S) :
    (s039AllBlocks S : Set (Finset (Fin 24))).PairwiseDisjoint id := by
  intro I hI J hJ hne
  exact shortZero_disjoint_of_ne hAvoid
    (mem_s039AllBlocks.mp hI) (mem_s039AllBlocks.mp hJ) hne
end InverseZeroSum.Candidate3
