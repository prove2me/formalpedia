-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeSetT_card
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:27:13.246119+00:00
-- url     : https://prove2.me/submissions/2b62b522-902a-4a5f-806f-83b79ec49c1c

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution (p : PlaneIdx) :
    (planeSetT p).card = 9 := by
  revert p; decide +kernel
