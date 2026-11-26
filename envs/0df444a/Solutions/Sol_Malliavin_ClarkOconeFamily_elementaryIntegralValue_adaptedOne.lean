-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.elementaryIntegralValue_adaptedOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:49.220803+00:00
-- url     : https://prove2.me/submissions/529198f6-dc81-4ba4-b91a-fb0b5bc0f611

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_coeFn_elementaryIntegralValue
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
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
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b) :
    C.elementaryIntegralValue hab (adaptedOne (P := P) 𝓕 a) =
      brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a := by
  apply Lp.ext
  have hOne : (adaptedOne (P := P) 𝓕 a : W → ℝ) =ᵐ[P]
      fun _ => (1 : ℝ) := by
    change (Lp.const 2 P (1 : ℝ) : W → ℝ) =ᵐ[P] fun _ => (1 : ℝ)
    exact Lp.coeFn_const 2 P (1 : ℝ)
  filter_upwards [C.coeFn_elementaryIntegralValue hab (adaptedOne (P := P) 𝓕 a),
    hOne,
    Lp.coeFn_sub (brownianLp C.isPreBrownian b) (brownianLp C.isPreBrownian a),
    coeFn_brownianLp C.isPreBrownian b, coeFn_brownianLp C.isPreBrownian a]
    with w hvalue hone hsub hb ha
  rw [hvalue, hone, hsub]
  simp only [Pi.sub_apply]
  rw [hb, ha]
  simp only [one_mul]
end ClarkOconeFamily
end Malliavin
