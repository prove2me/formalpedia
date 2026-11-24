-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planePointT_surjective_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:59.008218+00:00
-- url     : https://prove2.me/submissions/414ef58d-57aa-44cd-82b2-b83b19c20bc4

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ p : PlaneIdx, ∀ x : F3T,
      onPlaneTB p x = true → ∃ q : PlaneCoord, planePointT p q = x := by
  decide
end InverseZeroSum.Candidate3
