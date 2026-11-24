-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_eight_constant_blocks_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:04.967269+00:00
-- url     : https://prove2.me/submissions/d69eb4b0-c538-467d-80f4-868f53ce8765

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
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (h : S8RepresentativeSwapOutput S c) :
    blockUnion c.blocks = Finset.univ := by
  classical
  have hZero : (Finset.univ \ blockUnion c.blocks).card = 0 := by
    simpa [h.2.1] using c.remainder_card
  have hempty : Finset.univ \ blockUnion c.blocks = ∅ :=
    Finset.card_eq_zero.mp hZero
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    by_contra hn
    have hm : x ∈ Finset.univ \ blockUnion c.blocks :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hn⟩
    simpa [hempty] using hm
end InverseZeroSum.Candidate3
