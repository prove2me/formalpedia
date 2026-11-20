-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneReciprocalPower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:59:16.139667+00:00
-- url     : https://prove2.me/submissions/3f7c097e-c533-4384-a1aa-ac25d476b2e3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution (alpha r : ℝ) (hr : 0 < r) :
    (((r ^ (-alpha - 1) : ℝ) : ℂ)) =
      (((r ^ (alpha + 1) : ℝ) : ℂ))⁻¹ := by
  have he : -alpha - 1 = -(alpha + 1) := by ring
  rw [he, Real.rpow_neg hr.le]
  exact Complex.ofReal_inv _
