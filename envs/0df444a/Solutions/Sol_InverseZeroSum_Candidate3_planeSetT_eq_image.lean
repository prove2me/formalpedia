-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeSetT_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:31:46.490899+00:00
-- url     : https://prove2.me/submissions/df0a32e6-a4c2-4985-ba0b-1e8815b05bad

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution (p : PlaneIdx) :
    planeSetT p = Finset.univ.image (planePointT p) := by
  revert p; decide +kernel
