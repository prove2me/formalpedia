-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planePointT_onPlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:58.225435+00:00
-- url     : https://prove2.me/submissions/1635cc7f-b6b7-4bc0-b30b-8e850d5fd64d

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ p : PlaneIdx, ∀ q : PlaneCoord,
      onPlaneTB p (planePointT p q) = true := by
  decide
end InverseZeroSum.Candidate3
