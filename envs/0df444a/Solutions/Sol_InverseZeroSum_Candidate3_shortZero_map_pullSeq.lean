-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortZero_map_pullSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:04.073798+00:00
-- url     : https://prove2.me/submissions/3fe122e1-313c-46e4-b25e-75e38649093b

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
theorem _root_.solution {m n : ℕ} (S : PosSeq n) (e : Fin m ↪ Fin n)
    {I : Finset (Fin m)} (h : ShortZero (pullSeq S e) I) :
    ShortZero S (I.map e) := by
  classical
  simpa [ShortZero, posSum, pullSeq] using h
end InverseZeroSum.Candidate3
