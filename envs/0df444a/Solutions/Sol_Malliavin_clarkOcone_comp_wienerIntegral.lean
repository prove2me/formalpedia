-- Prove2me | solution 1 for Malliavin.clarkOcone_comp_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:57.78661+00:00
-- url     : https://prove2.me/submissions/77e0813a-4674-4eaf-8762-c116bd0852fb

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_predictableDerivative_compWienerIntegralD12
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
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (memLp_comp_of_deriv_le P hφ hK (wienerIntegral C.isPreBrownian g)).toLp _ =
      expectationL2 ((memLp_comp_of_deriv_le P hφ hK (wienerIntegral C.isPreBrownian g)).toLp _)
        + C.itoIntegral (predictableProjection 𝓕
          (tensor g ((memLp_deriv_comp hφ hK (wienerIntegral C.isPreBrownian g)).toLp _))) := by
  have h := clarkOcone C (compWienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated hφ hK g)
  rw [clarkOconeIntegral, predictableDerivative_compWienerIntegralD12] at h
  exact h
end Malliavin
