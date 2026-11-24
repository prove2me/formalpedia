-- Prove2me | solution 1 for Kyprianou.Ch02.poissonNonnegativeIntegralLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:04:16.154797+00:00
-- url     : https://prove2.me/submissions/74ee6a20-bfb4-4e3e-82b2-bfd2ee9ea993

import Mathlib
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_Kyprianou_poissonRandomMeasureIntegralLaws
import Theorems.Thm_Kyprianou_ProofPreparation_measurable_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (m : Measure ℝ) [SigmaFinite m]
    (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hint : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧ Q (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ ξ : ℝ, charFun Q ξ =
        Complex.exp (∫ x, (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂m) := by
  obtain ⟨Ω, mΩ, P, K, Y, hP, hfamily⟩ := ProbabilityTheory.exists_isPoissonPointFamily m
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  let J : Ω → ℝ := fun ω => ∫ x, f x ∂ProbabilityTheory.poissonRandomMeasure K Y ω
  have hJ : Measurable J := by
    have hL := Kyprianou.ProofPreparation.measurable_lintegral_poissonRandomMeasure
      P m K Y hfamily (g := fun x : ℝ => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp hf)
    have heq : J = fun ω => (∫⁻ x, ENNReal.ofReal (f x) ∂
        ProbabilityTheory.poissonRandomMeasure K Y ω).toReal := by
      funext ω
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable
    rw [heq]
    exact ENNReal.measurable_toReal.comp hL
  refine ⟨P.map J, Measure.isProbabilityMeasure_map hJ.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_apply hJ measurableSet_Iio]
    have h_empty : J ⁻¹' Set.Iio (0 : ℝ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      change J ω < 0 at hω
      exact (not_lt_of_ge (show 0 ≤ J ω from integral_nonneg hf0)) hω
    rw [h_empty, measure_empty]
  · exact (Kyprianou.poissonRandomMeasureIntegralLaws P m K Y hfamily f hf).2.1 hint
