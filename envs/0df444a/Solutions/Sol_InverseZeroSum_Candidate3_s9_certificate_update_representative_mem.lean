-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_certificate_update_representative_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:59.92969+00:00
-- url     : https://prove2.me/submissions/80392ef3-19f0-4b44-b8cf-9c119a70a19e

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
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24} (hy : y ∈ c.blocks j) :
    ∀ k, (Function.update rep j y) k ∈ c.blocks k := by
  intro k
  by_cases hkj : k = j
  · subst k
    simpa using hy
  · simpa [Function.update, hkj] using hRep k
end InverseZeroSum.Candidate3
