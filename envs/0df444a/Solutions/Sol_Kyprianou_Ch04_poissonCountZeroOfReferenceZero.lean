-- Prove2me | solution 1 for Kyprianou.Ch04.poissonCountZeroOfReferenceZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:51:48.215913+00:00
-- url     : https://prove2.me/submissions/9e237979-fe0f-4157-ab5f-50d0464efde5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

/-- A measurable region of zero reference intensity carries no Poisson mass almost surely. -/
theorem solution
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (A : Set (ℝ × E))
    (hA : MeasurableSet A) (h0 : referenceIntensity ν A = 0) :
    ∀ᵐ ω ∂P, N.N ω A = 0 := by
  have hf : referenceIntensity ν A ≠ ⊤ := by rw [h0]; simp
  have hi := LevyStochCalc.Poisson.Compensated.compensated_sq_integrable N hA hf
  have he := LevyStochCalc.Poisson.Compensated.compensated_second_moment N hA hf
  rw [h0, ENNReal.toReal_zero] at he
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (N.compensated A ω))) hi).mp he
  filter_upwards [hz, N.integer_valued hA hf] with ω hw hN
  obtain ⟨n, hn⟩ := hN
  have hc : N.compensated A ω = 0 := by
    change (N.compensated A ω)^2 = 0 at hw
    nlinarith [hw]
  rw [PoissonRandomMeasure.compensated, h0, ENNReal.toReal_zero, sub_zero, hn,
    ENNReal.toReal_natCast] at hc
  have hn0 : n = 0 := by exact_mod_cast hc
  simp [hn, hn0]
