-- Prove2me | solution 1 for InverseZeroSum.Candidate3.mem_s039AllBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:55.497243+00:00
-- url     : https://prove2.me/submissions/3b0a6366-f180-410a-8c51-73f26b7a0da3

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
theorem _root_.solution {S : PosSeq 24} {I : Finset (Fin 24)} :
    I ∈ s039AllBlocks S ↔ ShortZero S I := by
  classical
  simp [s039AllBlocks]
end InverseZeroSum.Candidate3
