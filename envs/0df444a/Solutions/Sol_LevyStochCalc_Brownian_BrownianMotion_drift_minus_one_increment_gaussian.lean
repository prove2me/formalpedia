-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_increment_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:22:15.151905+00:00
-- url     : https://prove2.me/submissions/236e682c-f226-4e1a-b7c3-29cc2eec3c3c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasLaw (fun ω => (W.W t ω - W.W s ω) - (t - s))
      (gaussianReal (-(t - s)) ⟨t - s, by linarith⟩) P := by
  have hm : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  have h : HasLaw (fun ω => W.W t ω - W.W s ω) (gaussianReal 0 ⟨t - s, by linarith⟩) P :=
    ⟨hm.aemeasurable, W.increment_gaussian hs hst⟩
  have h2 := HasLaw.fun_comp (Y := fun z : ℝ => z - (t - s))
    ⟨(measurable_id.sub_const _).aemeasurable, rfl⟩ h
  erw [gaussianReal_map_sub_const, zero_sub] at h2
  exact h2
