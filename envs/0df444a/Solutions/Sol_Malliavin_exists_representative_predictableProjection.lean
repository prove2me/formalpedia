-- Prove2me | solution 1 for Malliavin.exists_representative_predictableProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:45.657455+00:00
-- url     : https://prove2.me/submissions/35c6472e-979b-4493-8993-4d48e3f06aeb

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_setIntegral_timeSection_eq_condExp_ae
import Theorems.Thm_Malliavin_stronglyMeasurable_timeSection_of_predictable

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (U : TimeProcessL2 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ t, StronglyMeasurable[𝓕 t] fun ω ↦ G (t, ω)) ∧
      ∀ (a : ℝ≥0) (A : Set W), MeasurableSet[𝓕 a] A →
        ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
          ∫ ω in A, G (t, ω) ∂P
            = ∫ ω in A, (P[(fun ω ↦ U (t, ω)) | 𝓕 t]) ω ∂P := by
  have hmeas : AEStronglyMeasurable[𝓕.predictable]
      ((predictableProjection 𝓕 U : TimeProcessL2 P) : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := lpMeas.aestronglyMeasurable _
  refine ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk, fun t ↦
    stronglyMeasurable_timeSection_of_predictable 𝓕 hmeas.stronglyMeasurable_mk t,
    fun a A hA ↦ ?_⟩
  have hsec := Measure.ae_ae_of_ae_prod hmeas.ae_eq_mk
  filter_upwards [setIntegral_timeSection_eq_condExp_ae 𝓕 U hA, hsec] with t ht hst hat
  rw [← ht hat]
  exact setIntegral_congr_ae (𝓕.le a A hA) (hst.mono fun ω hω _ ↦ hω.symm)
end Malliavin
