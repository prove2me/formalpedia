-- Prove2me | solution 1 for Malliavin.exists_representative_predictableDerivative_integral_condExpKernel_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:09:00.559964+00:00
-- url     : https://prove2.me/submissions/d1296010-5a47-4320-be37-c0c836c73281

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp_natural
import Theorems.Thm_Malliavin_condExp_timeSection_ae_eq_integral_condExpKernel


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
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
      (predictableDerivative C F : ℝ≥0 × W → ℝ)
        =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          fun w ↦ ∫ y, (C.timeDerivative (mderivD12 P F)) (t, y)
            ∂condExpKernel P (𝓕 t) w := by
  obtain ⟨G, hG, hGae, hsection⟩ :=
    exists_representative_predictableDerivative_condExp_natural C F
  refine ⟨G, hG, hGae, ?_⟩
  filter_upwards [hsection,
    condExp_timeSection_ae_eq_integral_condExpKernel 𝓕
      (C.timeDerivative (mderivD12 P F))] with t hsection_t hkernel_t ht
  exact (hsection_t ht).trans hkernel_t
end Malliavin
