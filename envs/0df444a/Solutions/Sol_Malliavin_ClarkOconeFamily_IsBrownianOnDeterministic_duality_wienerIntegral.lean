-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.duality_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:43:02.264233+00:00
-- url     : https://prove2.me/submissions/4bc86f4f-201c-442b-bf77-7154b4dabac2

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_deterministicTimeEmbedding_eq_tensor
import Theorems.Thm_Malliavin_predictableProjection_deterministic
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_deterministicIntegral_eq_wienerIntegral
import Theorems.Thm_Malliavin_ClarkOconeFamily_deterministicIntegral_apply
import Theorems.Thm_Malliavin_ClarkOconeFamily_timeDerivative_apply
import Theorems.Thm_Malliavin_integral_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_wienerIntegral
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



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
namespace ClarkOconeFamily.IsBrownianOnDeterministic
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (g h : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪wienerIntegral C.isPreBrownian g - expectationL2 (wienerIntegral C.isPreBrownian g),
        C.itoIntegral (deterministicPredictableEmbedding 𝓕 h)⟫_ℝ =
      ⟪predictableProjection 𝓕
        (C.timeDerivative (mderivClosure P (wienerIntegral C.isPreBrownian g))),
        deterministicPredictableEmbedding 𝓕 h⟫_ℝ := by
  -- left side: `E F = 0` and the integral of `h ⊗ 1` is `J₁ h`
  have hE : expectationL2 (wienerIntegral C.isPreBrownian g) = 0 := by
    unfold expectationL2
    rw [integral_wienerIntegral]
    exact map_zero _
  have hI : C.itoIntegral (deterministicPredictableEmbedding 𝓕 h) =
      wienerIntegral C.isPreBrownian h := by
    have := congrArg (fun φ ↦ φ h) hC.deterministicIntegral_eq_wienerIntegral
    simpa [ClarkOconeFamily.deterministicIntegral_apply] using this
  rw [hE, sub_zero, hI, inner_wienerIntegral]
  -- right side: `Dₜ (J₁ g) = g ⊗ 1`, fixed by the predictable projection
  rw [ClarkOconeFamily.timeDerivative_apply, timeDerivative_mderivClosure_wienerIntegral
    C.isPreBrownian C.coordinate C.coordinate_apply C.generated,
    ← deterministicTimeEmbedding_eq_tensor, predictableProjection_deterministic]
  rw [Submodule.coe_inner, ← LinearIsometry.inner_map_map (deterministicTimeEmbedding (P := P))]
  rfl
end ClarkOconeFamily.IsBrownianOnDeterministic
end Malliavin
