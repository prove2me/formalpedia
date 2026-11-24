-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_eight_constant_block_card
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:31:35.052331+00:00
-- url     : https://prove2.me/submissions/050250d9-4fbb-4327-88ec-fc626acf80b5

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000


theorem solution {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 8) (h : S8RepresentativeSwapOutput S c)
    (j : Fin c.s) :
    (c.blocks j).card = 3 := by
  have hlt : j.val < c.l := by have hj := j.isLt; have hl := h.1; omega
  simpa [hlt] using c.block_card j
