-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_marginal_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:07:10.849687+00:00
-- url     : https://prove2.me/submissions/7fc5042a-fa1e-4d27-adcc-3a85307227c3

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (fun ω => W.W (t : ℝ) ω - (t : ℝ))
      ((gaussianReal 0 t).map (fun z : ℝ => z - (t : ℝ))) P := by
  have h := LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable W t
  exact HasLaw.comp (X := W.W (t : ℝ)) (Y := fun z : ℝ => z - (t : ℝ)) ⟨by fun_prop, rfl⟩ h
