-- Prove2me | solution 1 for Malliavin.exists_representative_predictableDerivative_condExp_of_leftContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:46.907166+00:00
-- url     : https://prove2.me/submissions/7cf9c237-bf00-47bd-9b7e-615fe2e06a10

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp

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
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P)
    (hlc : ∀ t : ℝ≥0, 0 < t → filtrationPred 𝓕 t = 𝓕 t) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] := by
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_representative_predictableDerivative_condExp C F
  refine ⟨G, hG1, hG2, ?_⟩
  filter_upwards [hG3] with t ht hat
  rw [← hlc t hat]
  exact ht hat
end Malliavin
