-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeValueT_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:10.337795+00:00
-- url     : https://prove2.me/submissions/4bc8cf98-41e8-4368-90ba-62bd2c5162a4

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ d : Fin 13, ∀ x y : F3T,
      planeValueT d (x + y) = planeValueT d x + planeValueT d y := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 500000 in
    decide
end InverseZeroSum.Candidate3
