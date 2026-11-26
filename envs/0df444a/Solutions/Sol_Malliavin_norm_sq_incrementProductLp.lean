-- Prove2me | solution 1 for Malliavin.norm_sq_incrementProductLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:33.170793+00:00
-- url     : https://prove2.me/submissions/8d682124-5210-49ab-ad87-05860450bfec

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_coeFn_incrementProductLp
import Theorems.Thm_Malliavin_indepFun_incr_incr
import Theorems.Thm_Malliavin_integral_incr_sq
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
theorem _root_.solution (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    ‖incrementProductLp hB a b c d‖ ^ 2 = ((b : ℝ) - a) * ((d : ℝ) - c) := by
  have hX : MemLp (fun ω ↦ B b ω - B a ω) 2 P :=
    (memLp_eval hB b (p := 2) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB a (p := 2) ENNReal.ofNat_ne_top)
  have hY : MemLp (fun ω ↦ B d ω - B c ω) 2 P :=
    (memLp_eval hB d (p := 2) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB c (p := 2) ENNReal.ofNat_ne_top)
  have hsq := (indepFun_incr_incr hB hab hbc hcd).integral_fun_comp_mul_comp
    (f := fun x : ℝ ↦ x ^ 2) (g := fun x : ℝ ↦ x ^ 2) hX.aemeasurable hY.aemeasurable
    (by fun_prop) (by fun_prop)
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_incr_sq hB hab,
    ← integral_incr_sq hB hcd, ← hsq]
  apply integral_congr_ae
  filter_upwards [coeFn_incrementProductLp hB a b c d] with ω h1
  rw [h1]
  simp only [RCLike.inner_apply, conj_trivial]
  ring
end Malliavin
