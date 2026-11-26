-- Prove2me | solution 1 for Malliavin.integral_odd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:52:26.601937+00:00
-- url     : https://prove2.me/submissions/f3ded9d7-0ecb-4ba7-957c-90bdbd6572bb

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (I : Finset ℝ≥0)
    {f : (I → ℝ) → ℝ} (hf : Measurable f) (hodd : ∀ x, f (-x) = -f x) :
    ∫ ω, f (I.restrict (B · ω)) ∂P = 0 := by
  have h1 := (hB.hasLaw I).integral_comp (f := f) hf.aestronglyMeasurable
  have h2 := (hB.neg.hasLaw I).integral_comp (f := f) hf.aestronglyMeasurable
  have e : (f ∘ fun ω ↦ I.restrict ((-B) · ω)) = fun ω ↦ -f (I.restrict (B · ω)) := by
    funext ω
    rw [Function.comp_apply, ← hodd]
    rfl
  rw [e, integral_neg] at h2
  simp only [Function.comp_apply] at h1
  linarith
end Malliavin
