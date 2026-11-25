-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.compensated_cross_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:46:29.458799+00:00
-- url     : https://prove2.me/submissions/130f7d85-d643-4a26-82fc-0797706230ba

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001
import Theorems.Thm_LevyStochCalc_Poisson_Compensated_compensated_sq_integrable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The product of two square-integrable compensated Poisson cells is L1. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    {E : Type} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBf : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    Integrable (fun ω => N.compensated B ω * N.compensated C ω) P := by
  have hBsq : Integrable (fun ω => (N.compensated B ω)^2) P :=
    LevyStochCalc.Poisson.Compensated.compensated_sq_integrable N hB hBf
  have hCsq : Integrable (fun ω => (N.compensated C ω)^2) P :=
    LevyStochCalc.Poisson.Compensated.compensated_sq_integrable N hC hCf
  have hBm : Measurable (fun ω => N.compensated B ω) := by
    change Measurable (fun ω => (N.N ω B).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
    exact (ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _
  have hCm : Measurable (fun ω => N.compensated C ω) := by
    change Measurable (fun ω => (N.N ω C).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν C).toReal)
    exact (ENNReal.measurable_toReal.comp (N.measurable_eval hC)).sub_const _
  refine Integrable.mono'
    ((hBsq.const_mul (1/2 : ℝ)).add (hCsq.const_mul (1/2 : ℝ)))
    (hBm.mul hCm).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  change |N.compensated B ω * N.compensated C ω| ≤
    (1/2 : ℝ) * (N.compensated B ω)^2 +
      (1/2 : ℝ) * (N.compensated C ω)^2
  rw [abs_mul]
  have hs := sq_nonneg (|N.compensated B ω| - |N.compensated C ω|)
  nlinarith [sq_abs (N.compensated B ω), sq_abs (N.compensated C ω)]
