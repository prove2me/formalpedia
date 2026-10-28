-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_gaussian_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:09:41.980713+00:00
-- url     : https://prove2.me/submissions/753b5eeb-7e5e-4504-a52f-598f6370b01c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (fun ω => W.W (t : ℝ) ω - (t : ℝ))
      (gaussianReal (-(t : ℝ)) t) P := by
  have h := LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable W t
  have h2 := HasLaw.comp (X := W.W (t : ℝ)) (Y := fun z : ℝ => z - (t : ℝ))
    ⟨by fun_prop, rfl⟩ h
  have e : (gaussianReal 0 t).map (fun z : ℝ => z - (t : ℝ)) = gaussianReal (-(t : ℝ)) t := by
    rw [gaussianReal_map_sub_const]; simp
  rw [e] at h2
  exact h2
