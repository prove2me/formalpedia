-- Prove2me | solution 2 for InverseZeroSum.Candidate3.s056_eight_constant_block_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:22.310953+00:00
-- url     : https://prove2.me/submissions/acbda18c-51c8-43b1-84ee-b5aaa24f79a9

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
    (hs : c.s = 8) (h : S8RepresentativeSwapOutput S c)
    (j : Fin c.s) :
    (c.blocks j).card = 3 := by
  have hj : j.val < c.l := by
    rw [h.1]
    simpa [hs] using j.isLt
  simpa [hj] using c.block_card j
end InverseZeroSum.Candidate3
