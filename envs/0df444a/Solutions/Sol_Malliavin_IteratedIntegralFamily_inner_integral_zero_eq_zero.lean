-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.inner_integral_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:29.797883+00:00
-- url     : https://prove2.me/submissions/c2bf2cd8-70c4-451e-b14f-91b391dd1b16

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
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
namespace IteratedIntegralFamily
theorem _root_.solution (J : IteratedIntegralFamily P)
    {Y : RandomL2 P} (hY : ∫ ω, Y ω ∂P = 0) (f : IteratedKernel 0) :
    ⟪Y, J.integral 0 f⟫_ℝ = 0 := by
  rw [L2.inner_def]
  have h := J.zeroOrder f
  calc ∫ ω, ⟪Y ω, J.integral 0 f ω⟫_ℝ ∂P
      = ∫ ω, Y ω * (∫ t, f t ∂iteratedKernelMeasure 0) ∂P := by
        apply integral_congr_ae
        filter_upwards [h] with ω hω
        rw [hω]
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ = 0 := by rw [integral_mul_const, hY, zero_mul]
end IteratedIntegralFamily
end Malliavin
