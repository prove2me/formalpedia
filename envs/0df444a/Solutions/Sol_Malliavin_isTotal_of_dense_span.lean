-- Prove2me | solution 1 for Malliavin.isTotal_of_dense_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:02.569095+00:00
-- url     : https://prove2.me/submissions/50f4d822-e82e-4b8d-befe-9e5079ce4ac0

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace Malliavin
theorem _root_.solution (T : κ → F)
    (hT : Dense (Submodule.span ℝ (Set.range T) : Set F)) : IsTotal T := by
  intro η hη
  apply hT.eq_zero_of_inner_left ℝ
  intro v hv
  rw [SetLike.mem_coe] at hv
  induction hv using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨k, rfl⟩ := ht
    exact hη k
  | zero => simp only [inner_zero_right]
  | add u v _ _ hu hv => simp [inner_add_right, hu, hv]
  | smul c u _ hu => simp [inner_smul_right, hu]
end Malliavin
