-- Prove2me | solution 1 for Malliavin.exists_representative_predictableDerivative_condExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:56.722377+00:00
-- url     : https://prove2.me/submissions/afd19ca3-19b1-4607-97a1-56e7f2f13449

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_timeSection_predictableProjection_ae_eq_condExp
import Theorems.Thm_Malliavin_secondCountableTopology_randomL2_of_isWienerGenerated


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
namespace Malliavin
theorem _root_.solution
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | filtrationPred 𝓕 t] := by
  have _i : SecondCountableTopology (RandomL2 P) :=
    secondCountableTopology_randomL2_of_isWienerGenerated C.isPreBrownian C.generated
  have hmeas : AEStronglyMeasurable[𝓕.predictable]
      ((predictableDerivative C F : TimeProcessL2 P) : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := lpMeas.aestronglyMeasurable _
  exact ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk,
    timeSection_predictableProjection_ae_eq_condExp 𝓕 (C.timeDerivative (mderivD12 P F))
      hmeas.stronglyMeasurable_mk hmeas.ae_eq_mk⟩
end Malliavin
