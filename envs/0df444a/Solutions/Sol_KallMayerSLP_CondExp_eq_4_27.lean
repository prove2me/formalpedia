-- Prove2me | solution 1 for KallMayerSLP.CondExp.eq_4_27
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:12:52.648432+00:00
-- url     : https://prove2.me/submissions/3663ab6d-5564-413c-932c-3d39e7ec8af2

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_IsQuantile
import Definitions.Def_KallMayerSLP_CondExp_condTailMean

open MeasureTheory

open KallMayerSLP.CondExp in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Measurable ϑ) (hint : Integrable ϑ μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (ν : ℝ) (hν : IsQuantile μ ϑ α ν) :
    0 < μ.real {ω | ν ≤ ϑ ω} ∧
      condTailMean μ ϑ ν = ν + 1 / μ.real {ω | ν ≤ ϑ ω} * ∫ ω, max (ϑ ω - ν) 0 ∂μ := by
  have hS : MeasurableSet {ω | ν ≤ ϑ ω} := measurableSet_le measurable_const hϑ
  have hpos : 0 < μ.real {ω | ν ≤ ϑ ω} := lt_of_lt_of_le (by linarith) hν.2
  refine ⟨hpos, ?_⟩
  have hmax : (fun ω => max (ϑ ω - ν) 0) = {ω | ν ≤ ϑ ω}.indicator (fun ω => ϑ ω - ν) := by
    funext ω
    by_cases h : ν ≤ ϑ ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ν ≤ ϑ ω} from h)]
      exact max_eq_left (by linarith)
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ν ≤ ϑ ω} from h)]
      exact max_eq_right (by linarith)
  have hI : ∫ ω, max (ϑ ω - ν) 0 ∂μ =
      (∫ ω in {ω | ν ≤ ϑ ω}, ϑ ω ∂μ) - μ.real {ω | ν ≤ ϑ ω} * ν := by
    rw [hmax, integral_indicator hS, integral_sub hint.integrableOn (integrable_const ν),
      setIntegral_const, smul_eq_mul]
  rw [hI]
  unfold condTailMean
  field_simp
  ring
