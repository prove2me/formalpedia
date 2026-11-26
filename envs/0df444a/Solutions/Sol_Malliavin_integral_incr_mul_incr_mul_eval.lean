-- Prove2me | solution 1 for Malliavin.integral_incr_mul_incr_mul_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:16.060481+00:00
-- url     : https://prove2.me/submissions/6e52f6a6-1fcb-44c8-acbd-44764acb8506

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_integral_odd_eq_zero
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
theorem _root_.solution (hB : IsPreBrownianReal B P) (a b c d t : ℝ≥0) :
    ∫ ω, (B b ω - B a ω) * (B d ω - B c ω) * B t ω ∂P = 0 := by
  let I : Finset ℝ≥0 := {a, b, c, d, t}
  have ha : a ∈ I := by simp [I]
  have hb : b ∈ I := by simp [I]
  have hc : c ∈ I := by simp [I]
  have hd : d ∈ I := by simp [I]
  have ht : t ∈ I := by simp [I]
  have := integral_odd_eq_zero hB I
    (f := fun x ↦ (x ⟨b, hb⟩ - x ⟨a, ha⟩) * (x ⟨d, hd⟩ - x ⟨c, hc⟩) * x ⟨t, ht⟩)
    (by fun_prop) (fun x ↦ by simp only [Pi.neg_apply]; ring)
  simpa [Finset.restrict] using this
end Malliavin
