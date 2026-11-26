-- Prove2me | solution 1 for Malliavin.cylinderPartialExp_oneCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:43.755799+00:00
-- url     : https://prove2.me/submissions/9451c401-b544-4f78-a37b-9d5c53420e46

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
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
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
variable {g : ℝ → ℝ}
namespace Malliavin
theorem _root_.solution (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0)
    (hd : MemLp (fun w ↦ deriv g (B T w)) 2 P) :
    cylinderPartialExp (P := P) L hL (contDiff_oneCoord hg) hC hc
        (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T) 0 =
      hd.toLp _ := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL (contDiff_oneCoord hg)
      (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T) (expGrowth_coord_le hC hc _)
      (integrable_expGrowth_sq P C c _) 0),
    MemLp.coeFn_toLp hd] with w h1 h2
  rw [cylinderPartialExp, cylinderPartialD, h1, h2, fderiv_oneCoord hg]
  simp only [Fin.isValue, smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
end Malliavin
