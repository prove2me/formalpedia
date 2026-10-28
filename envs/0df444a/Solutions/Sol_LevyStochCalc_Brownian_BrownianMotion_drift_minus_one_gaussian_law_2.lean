-- Prove2me | solution 2 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_gaussian_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:10:39.735297+00:00
-- url     : https://prove2.me/submissions/adb71e32-19af-4cb1-8e89-81e5069d4157

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.Probability.Distributions.Gaussian.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (fun ω => W.W (t : ℝ) ω - (t : ℝ))
      (gaussianReal (-(t : ℝ)) t) P := by
  simpa only [zero_sub] using
    (gaussianReal_sub_const (W.hasLaw_eval_readable t) (t : ℝ))
