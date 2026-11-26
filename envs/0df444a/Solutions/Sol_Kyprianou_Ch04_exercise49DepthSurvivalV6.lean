-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthSurvivalV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:36:39.614949+00:00
-- url     : https://prove2.me/submissions/6cf36042-7782-4d7f-bc4a-e4942b08cf09

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalClockIffV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthIsLUBV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hB : BddAbove (Set.range (fun t => -Y t)))
    (x : ℝ) (hx : 0 ≤ x) :
    (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal ≤ x ↔
      (sInf {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x + Y t < 0}) = ⊤ := by
  rw [Kyprianou.Ch04.exercise49SurvivalClockIffV1 Y h0 x hx]
  have hL := Kyprianou.Ch04.exercise49RationalDepthIsLUBV1 Y h0 hr hB
  constructor
  · intro h t
    have ht := hL.1 (Set.mem_range_self t)
    linarith
  · intro h
    apply hL.2
    rintro z ⟨t,rfl⟩
    linarith [h t]
