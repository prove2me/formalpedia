-- Prove2me | solution 1 for Malliavin.integral_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:09.976982+00:00
-- url     : https://prove2.me/submissions/1d6336d6-943c-4ccd-96c0-50276d3f40e3

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_integral_eq_inner_const
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
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ∫ ω, wienerIntegral hB f ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hB0 : ∀ t, ⟪brownianLp hB t, Lp.const 2 P (1 : ℝ)⟫_ℝ = 0 := fun t ↦ by
    rw [← integral_eq_inner_const, integral_congr_ae (coeFn_brownianLp hB t), hB.integral_eval]
  rw [integral_eq_inner_const]
  refine denseRange_stepToLp.induction_on f ?_ ?_
  · exact isClosed_eq ((wienerIntegral hB).continuous.inner continuous_const) continuous_const
  · intro v
    rw [wienerIntegral_stepToLp]
    unfold stepToRandom
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, real_inner_smul_left,
      hB0, mul_zero, Finset.sum_const_zero]
end Malliavin
