-- Prove2me | solution 1 for Kyprianou.Ch01.stableBelowOneCutoffComplexMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:42:02.459706+00:00
-- url     : https://prove2.me/submissions/443f7a5f-6bc3-4149-87c6-aa94ee675a42

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerSet
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioi (0 : ℝ),
      (if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0) ∂volume) =
      (((1 / (1 - alpha) : ℝ) : ℂ)) := by
  calc
    (∫ r in Set.Ioi (0 : ℝ),
        (if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0) ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ),
        (Set.Iio (1 : ℝ)).indicator
          (fun t : ℝ => (((t ^ (-alpha) : ℝ) : ℂ))) r ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases h : r < 1
        · simp [Set.indicator, h]
        · simp [Set.indicator, h]
    _ = (∫ r in Set.Ioo (0 : ℝ) 1,
          (((r ^ (-alpha) : ℝ) : ℂ)) ∂volume) := by
          rw [setIntegral_indicator measurableSet_Iio]
          rfl
    _ = (((1 / (1 - alpha) : ℝ) : ℂ)) := by
      change (∫ r : ℝ, (((r ^ (-alpha) : ℝ) : ℂ)) ∂
        (volume.restrict (Set.Ioo (0 : ℝ) 1))) = _
      exact_mod_cast
        (Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerSet
          alpha ha0 ha1)
