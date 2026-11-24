-- Prove2me | solution 1 for InverseZeroSum.Candidate3.f3t_self_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:12.423945+00:00
-- url     : https://prove2.me/submissions/5d860e73-81b2-4b78-b0f1-e11f95502bb1

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ x : F3T, x ≠ 0 → x + x ≠ 0 := by
  decide
end InverseZeroSum.Candidate3
