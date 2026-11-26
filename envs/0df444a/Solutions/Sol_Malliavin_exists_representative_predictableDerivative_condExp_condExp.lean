-- Prove2me | solution 1 for Malliavin.exists_representative_predictableDerivative_condExp_condExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:45.172114+00:00
-- url     : https://prove2.me/submissions/4ef4e10f-4b29-4275-9f81-5a46694969b4

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
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] |
            filtrationPred 𝓕 t] := by
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_representative_predictableDerivative_condExp C F
  refine ⟨G, hG1, hG2, ?_⟩
  filter_upwards [hG3] with t ht hat
  refine (ht hat).trans ?_
  refine (condExp_condExp_of_le ?_ (𝓕.le t)).symm
  exact iSup₂_le fun s hst ↦ 𝓕.mono hst.le
end Malliavin
