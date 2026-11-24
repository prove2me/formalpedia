-- Prove2me | solution 1 for InverseZeroSum.Candidate3.on_horizontalPlaneT_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:04.969874+00:00
-- url     : https://prove2.me/submissions/e556f5b6-7610-4493-ac08-849e3cf97af1

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (c : Fin 3) (x : F3T) :
    onPlaneTB (horizontalPlaneT c) x = true ↔ thirdCoordT x = c := by
  norm_num [onPlaneTB, horizontalPlaneT, thirdCoordT, planeValueT]
end InverseZeroSum.Candidate3
