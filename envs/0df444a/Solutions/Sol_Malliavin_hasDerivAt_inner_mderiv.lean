-- Prove2me | solution 1 for Malliavin.hasDerivAt_inner_mderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:28.81992+00:00
-- url     : https://prove2.me/submissions/32288811-ec79-4682-91eb-b3a2e987ce69

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
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {F : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (h : Space μ) :
    HasDerivAt (fun ε : ℝ ↦ F (x + ε • inclusion μ h)) ⟪mderiv μ F x, h⟫_ℝ 0 := by
  rw [inner_mderiv]
  have hline : HasDerivAt (fun ε : ℝ ↦ x + ε • inclusion μ h) ((1 : ℝ) • inclusion μ h) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (inclusion μ h)).const_add x
  rw [one_smul] at hline
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • inclusion μ h) := by
    simpa only [zero_smul, add_zero] using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hline
end Malliavin
