-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planePointT_sum_zero_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:00.838344+00:00
-- url     : https://prove2.me/submissions/e031a5dd-7ff3-4293-aa84-ae2a0b8c5f35

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ p : PlaneIdx, ∀ a b c : PlaneCoord,
      a + b + c = 0 →
      planePointT p a + planePointT p b + planePointT p c = 0 := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 500000 in
    decide
end InverseZeroSum.Candidate3
