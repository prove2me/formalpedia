-- Prove2me | solution 1 for Kyprianou.Ch04.compensatedCrossDisjointZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:41:38.514999+00:00
-- url     : https://prove2.me/submissions/92e6f6d2-bfea-40a1-b358-1cfa13cc19cb

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_disjointCompensatedCountsIndependent
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

/-- Cross-moment of two independent compensated Poisson counts. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hdisj : Disjoint B B') :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P = 0 := by
  have hi := Kyprianou.Ch04.disjointCompensatedCountsIndependent N hB hB' hdisj
  have hm : AEStronglyMeasurable (fun ω => N.compensated B ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun ω => N.compensated B' ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB')).sub_const _).aestronglyMeasurable
  rw [hi.integral_fun_mul_eq_mul_integral hm hm', compensated_mean_zero N hB hfin, zero_mul]
