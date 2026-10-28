-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_levy_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:20:47.903777+00:00
-- url     : https://prove2.me/submissions/6b9a15b6-b181-4cbd-bec9-1cc94c334b8a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_mgf
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (t : ℝ≥0) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ)))) P ∧
    (∫ ω, Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ))) ∂P) =
      Real.exp ((t : ℝ) * AvramDividend.Classical.laplaceExponent
        (-1) 1 (0 : Measure ℝ) θ) := by
  have h := BrownianMotion.drift_minus_one_mgf W t θ
  refine ⟨Integrable.of_integral_ne_zero (by rw [h]; exact (Real.exp_pos _).ne'), ?_⟩
  rw [h, AvramDividend.Classical.laplaceExponent_zero_jump_measure]
  congr 1; ring
