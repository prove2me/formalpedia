-- Prove2me | solution 1 for Kyprianou.Ch01.stableBelowOneCutoffComplexIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:55:03.529193+00:00
-- url     : https://prove2.me/submissions/b78b92f1-0b77-4878-8fab-3c582de02589

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerIntegrable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    IntegrableOn
      (fun r : ℝ => if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0)
      (Set.Ioi (0 : ℝ)) := by
  have hreal :=
    Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerIntegrable
      alpha ha0 ha1
  have hcomplex : IntegrableOn
      (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ)))
      (Set.Ioo (0 : ℝ) 1) := by
    change Integrable
      (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1))
    exact (Complex.ofRealLI.toContinuousLinearMap).integrable_comp hreal
  have hrest : Integrable
      (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).restrict
        (Set.Iio (1 : ℝ))) := by
    rw [Measure.restrict_restrict measurableSet_Iio]
    have hset : Set.Iio (1 : ℝ) ∩ Set.Ioi (0 : ℝ) =
        Set.Ioo (0 : ℝ) 1 := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
      tauto
    rw [hset]
    exact hcomplex
  have hind :
      Integrable
        ((Set.Iio (1 : ℝ)).indicator
          (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ))))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Iio).2 hrest
  apply (IntegrableOn.congr_fun hind ?_ measurableSet_Ioi)
  intro r hr
  by_cases h : r < 1
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]
