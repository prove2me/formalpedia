-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_mgf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:11:48.163471+00:00
-- url     : https://prove2.me/submissions/ac4d225d-fe3b-4228-b921-9f0d1b352220

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (t : ℝ≥0) (θ : ℝ) :
    (∫ ω, Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ))) ∂P) =
      Real.exp ((t : ℝ) * (-θ + θ ^ 2 / 2)) := by
  have h := LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable W t
  have h2 := HasLaw.comp (X := W.W (t : ℝ)) (Y := fun z : ℝ => z - (t : ℝ))
    ⟨by fun_prop, rfl⟩ h
  have e : (gaussianReal 0 t).map (fun z : ℝ => z - (t : ℝ)) = gaussianReal (-(t : ℝ)) t := by
    rw [gaussianReal_map_sub_const]; simp
  have hm := mgf_gaussianReal (X := fun ω => W.W (t : ℝ) ω - (t : ℝ)) (p := P)
    (by rw [← e]; exact h2.map_eq) θ
  rw [mgf] at hm
  rw [hm]
  congr 1
  ring
