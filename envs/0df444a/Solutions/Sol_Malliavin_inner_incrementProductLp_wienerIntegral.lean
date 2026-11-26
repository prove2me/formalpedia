-- Prove2me | solution 1 for Malliavin.inner_incrementProductLp_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:07.328554+00:00
-- url     : https://prove2.me/submissions/1619c397-ca3b-45c4-b196-5ac839873891

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_inner_incrementProductLp_brownianLp
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
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪incrementProductLp hB a b c d, wienerIntegral hB f⟫_ℝ = 0 := by
  refine denseRange_stepToLp.induction_on f ?_ ?_
  · exact isClosed_eq (continuous_const.inner (wienerIntegral hB).continuous) continuous_const
  · intro v
    rw [wienerIntegral_stepToLp]
    unfold stepToRandom
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, real_inner_smul_right,
      inner_incrementProductLp_brownianLp, mul_zero, Finset.sum_const_zero]
end Malliavin
