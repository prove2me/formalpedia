-- Prove2me | solution 1 for Malliavin.integral_incr_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:43.845903+00:00
-- url     : https://prove2.me/submissions/f528b5cc-fcf7-44bf-a611-efb7d8fbd22e

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
theorem _root_.solution (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ ω, (B b ω - B a ω) ^ 2 ∂P = (b : ℝ) - a := by
  have h : ⟪brownianLp hB b - brownianLp hB a, brownianLp hB b - brownianLp hB a⟫_ℝ =
      (b : ℝ) - a := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_brownianLp, inner_brownianLp,
      inner_brownianLp, inner_brownianLp, min_self, min_self,
      min_eq_right (by exact_mod_cast hab), min_eq_left (by exact_mod_cast hab)]
    ring
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a), coeFn_brownianLp hB a,
    coeFn_brownianLp hB b] with ω h1 ha hb
  rw [h1, Pi.sub_apply, ha, hb]
  simp only [sq, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
    abs_mul_abs_self]
end Malliavin
