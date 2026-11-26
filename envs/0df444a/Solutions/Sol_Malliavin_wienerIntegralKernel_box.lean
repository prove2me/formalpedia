-- Prove2me | solution 1 for Malliavin.wienerIntegralKernel_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:01.766256+00:00
-- url     : https://prove2.me/submissions/1344d5f4-409f-402a-bd24-155d529a7dfb

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_wienerIntegralKernel_boxKernel
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
theorem _root_.solution (hB : IsPreBrownianReal B P) (u v : Fin 1 → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) :
    (fun ω ↦ wienerIntegralKernel hB (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v := by
  have hu : u = fun _ ↦ u 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]
  have hv : v = fun _ ↦ v 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [hu, hv, wienerIntegralKernel_boxKernel hB (huv 0)]
  filter_upwards [Lp.coeFn_sub (brownianLp hB (v 0)) (brownianLp hB (u 0)),
    coeFn_brownianLp hB (v 0), coeFn_brownianLp hB (u 0)] with ω hsub hv0 hu0
  rw [hsub, Pi.sub_apply, hv0, hu0]
  simp only [Fin.isValue, chainIntegral, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_const,
    Finset.card_singleton, pow_one]
end Malliavin
