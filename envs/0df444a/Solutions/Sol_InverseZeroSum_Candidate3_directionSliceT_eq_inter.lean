-- Prove2me | solution 1 for InverseZeroSum.Candidate3.directionSliceT_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:26:28.332797+00:00
-- url     : https://prove2.me/submissions/cb97f70a-0cb2-4909-8d9b-0ca8107b4616

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution (A : Finset F3T) (d : Fin 13) (c : Fin 3) :
    directionSliceT A d c = A ∩ planeSetT (d, c) := by
  ext x; simp [directionSliceT,planeSetT,onPlaneTB]
