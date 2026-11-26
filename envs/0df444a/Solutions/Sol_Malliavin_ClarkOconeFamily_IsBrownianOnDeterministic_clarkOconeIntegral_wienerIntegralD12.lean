-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.clarkOconeIntegral_wienerIntegralD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:44.925065+00:00
-- url     : https://prove2.me/submissions/47b4e769-1e8d-4f49-8125-453ef8320eda

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
import Theorems.Thm_Malliavin_predictableDerivative_wienerIntegralD12
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
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
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
    (hC : C.IsBrownianOnDeterministic) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    clarkOconeIntegral C
        (wienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply C.generated g) =
      wienerIntegral C.isPreBrownian g := by
  unfold clarkOconeIntegral
  rw [predictableDerivative_wienerIntegralD12]
  have := congrArg (fun φ ↦ φ g) hC.deterministicIntegral_eq_wienerIntegral
  simpa [ClarkOconeFamily.deterministicIntegral_apply] using this
end ClarkOconeFamily.IsBrownianOnDeterministic
end Malliavin
