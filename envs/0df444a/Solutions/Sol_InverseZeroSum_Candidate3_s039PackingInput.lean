-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s039PackingInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:37.058961+00:00
-- url     : https://prove2.me/submissions/466e56d9-acb5-484d-a772-2ac934cb9b8c

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_threeTerm19Input
public import Theorems.Thm_InverseZeroSum_Candidate3_eta17Input
public import Theorems.Thm_InverseZeroSum_Candidate3_s039PackingInput_of_thresholds

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution : S039PackingInput :=
  s039PackingInput_of_thresholds threeTerm19Input eta17Input
end InverseZeroSum.Candidate3
