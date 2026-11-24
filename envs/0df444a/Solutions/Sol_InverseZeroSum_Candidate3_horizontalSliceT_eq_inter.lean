-- Prove2me | solution 1 for InverseZeroSum.Candidate3.horizontalSliceT_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:31:15.245105+00:00
-- url     : https://prove2.me/submissions/0ff1f4a1-7abe-47d2-a9f3-790f6edbb515

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution (A : Finset F3T) (c : Fin 3) :
    horizontalSliceT A c = A ∩ planeSetT (horizontalPlaneT c) := by
  ext x; simp [horizontalSliceT,planeSetT,onPlaneTB,horizontalPlaneT,planeValueT,thirdCoordT] <;> exact Finset.mem_filter
