-- Prove2me | solution 1 for Malliavin.clarkOcone_cylinder_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:46.469855+00:00
-- url     : https://prove2.me/submissions/1f851d5f-8002-4785-a640-5339c91fe642

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_predictableDerivative_cylinderGrowthD12
import Theorems.Thm_Malliavin_clarkOcone


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : 0 ≤ K) (hfg : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ K * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_growth_brownian C.coordinate C.coordinate_apply hf hK hfg t).toLp _ =
      expectationL2
          ((memLp_cylinder_growth_brownian C.coordinate C.coordinate_apply hf hK hfg t).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (∑ i, tensor (intervalIndicator (t i))
          (cylinderPartialGrowth C.coordinate C.coordinate_apply hf hK hfg' t i))) := by
  have h := clarkOcone C (cylinderGrowthD12 C.coordinate C.coordinate_apply hf hK hfg hfg' t)
  rw [clarkOconeIntegral, predictableDerivative_cylinderGrowthD12] at h
  exact h
end Malliavin
