-- Prove2me | solution 1 for InverseZeroSum.Candidate3.baseIndex_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:22:34.18409+00:00
-- url     : https://prove2.me/submissions/e83c4339-5d4d-4a8a-9e8a-4051980013e9

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (i : Fin 24) :
    (baseIndex i).val = i.val % 8 := by simp [baseIndex]
end InverseZeroSum.Candidate3
