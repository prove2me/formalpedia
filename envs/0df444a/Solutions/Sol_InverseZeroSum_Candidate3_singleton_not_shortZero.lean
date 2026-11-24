-- Prove2me | solution 1 for InverseZeroSum.Candidate3.singleton_not_shortZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:49.622934+00:00
-- url     : https://prove2.me/submissions/4e68f1b7-ab25-4820-9057-534b64e29714

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} (S : PosSeq n) (i : Fin n) :
    ¬ ShortZero S {i} := by
  intro h
  have hz : (S i : G) = 0 := by
    simpa [ShortZero, posSum] using h.2.2
  exact (S i).property hz
end InverseZeroSum.Candidate3
