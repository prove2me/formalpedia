-- Prove2me | solution 1 for InverseZeroSum.Candidate3.pair_plane_countT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:23.740808+00:00
-- url     : https://prove2.me/submissions/1dd58b53-b3a0-4c80-b571-e84ef883728d

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ x y : F3T, x ≠ y →
      ((Finset.univ : Finset PlaneIdx).filter
        (fun p => onPlaneTB p x = true ∧ onPlaneTB p y = true)).card = 4 := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 1000000 in
    decide
end InverseZeroSum.Candidate3
