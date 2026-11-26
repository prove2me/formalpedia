-- Prove2me | solution 1 for Malliavin.predictableDerivative_wienerIntegralD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:10.099191+00:00
-- url     : https://prove2.me/submissions/c4e53d5f-e00c-4b63-ae81-9208d267f676

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_deterministicTimeEmbedding_eq_tensor
import Theorems.Thm_Malliavin_predictableProjection_deterministic
import Theorems.Thm_Malliavin_ClarkOconeFamily_timeDerivative_apply
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_wienerIntegral


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
    (C : ClarkOconeFamily B P 𝓕) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C
        (wienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply C.generated g) =
      deterministicPredictableEmbedding 𝓕 g := by
  unfold predictableDerivative wienerIntegralD12
  rw [mderivD12_apply, ClarkOconeFamily.timeDerivative_apply,
    timeDerivative_mderivClosure_wienerIntegral C.isPreBrownian C.coordinate C.coordinate_apply
      C.generated, ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic]
end Malliavin
