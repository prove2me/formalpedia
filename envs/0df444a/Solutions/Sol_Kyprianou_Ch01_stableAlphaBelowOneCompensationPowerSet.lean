-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:28:23.530976+00:00
-- url     : https://prove2.me/submissions/fb25ad2a-30ca-4ec2-be34-5cd7485adc78

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerInterval
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Set
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioo (0 : ℝ) 1, r ^ (-alpha) ∂volume) =
      1 / (1 - alpha) := by
  calc
    (∫ r in Set.Ioo (0 : ℝ) 1, r ^ (-alpha) ∂volume) =
        ∫ r in (0 : ℝ)..1, r ^ (-alpha) ∂volume := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
    _ = 1 / (1 - alpha) :=
      Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerInterval
        alpha ha0 ha1
