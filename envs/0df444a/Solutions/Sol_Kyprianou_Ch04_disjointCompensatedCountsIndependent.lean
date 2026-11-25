-- Prove2me | solution 1 for Kyprianou.Ch04.disjointCompensatedCountsIndependent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:38:23.312137+00:00
-- url     : https://prove2.me/submissions/6730931e-3e4a-415b-aa32-51707543576b

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_disjointPoissonCountsIndependent
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

/-- Compensation by deterministic intensities preserves independence. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hdisj : Disjoint B B') :
    IndepFun (fun ω => N.compensated B ω) (fun ω => N.compensated B' ω) P := by
  have h := Kyprianou.Ch04.disjointPoissonCountsIndependent N hB hB' hdisj
  have heq : (fun ω => N.compensated B ω) =
      (fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν B).toReal) ∘
        (fun ω => N.N ω B) := by
    funext ω
    rfl
  have heq' : (fun ω => N.compensated B' ω) =
      (fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν B').toReal) ∘
        (fun ω => N.N ω B') := by
    funext ω
    rfl
  rw [heq, heq']
  exact h.comp (ENNReal.measurable_toReal.sub_const _)
    (ENNReal.measurable_toReal.sub_const _)
