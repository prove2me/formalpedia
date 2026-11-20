-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.tiltedScale_undo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:48:56.448943+00:00
-- url     : https://prove2.me/submissions/4b326329-7739-406b-9e90-e29b6ccdcadd

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_A
set_option autoImplicit false

open Kyprianou.Ch08

theorem solution (c x : ℝ) (W : ℝ → ℝ) :
    Real.exp (c * x) * tiltedScale c W x = W x := by
  rw [tiltedScale]
  calc
    Real.exp (c * x) * (Real.exp (-c * x) * W x) =
        (Real.exp (c * x) * Real.exp (-c * x)) * W x := by ring
    _ = W x := by
      rw [← Real.exp_add]
      have hz : c * x + -c * x = 0 := by ring
      simp [hz]
