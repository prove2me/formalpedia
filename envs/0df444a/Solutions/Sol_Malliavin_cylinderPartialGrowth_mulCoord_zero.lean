-- Prove2me | solution 1 for Malliavin.cylinderPartialGrowth_mulCoord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:43.718343+00:00
-- url     : https://prove2.me/submissions/7f5b369c-7437-40b6-acaa-c35f980f2bff

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
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution (S T : ℝ≥0) :
    cylinderPartialGrowth (P := P) L hL contDiff_mulCoord zero_le_two norm_fderiv_mulCoord_le
        ![S, T] 0 = (memLp_brownian L hL T).toLp _ := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL contDiff_mulCoord
      norm_fderiv_mulCoord_le ![S, T] (growth_coord_le zero_le_two _)
      (integrable_growth_sq P 2 _) 0),
    MemLp.coeFn_toLp (memLp_brownian L hL T)] with w h1 h2
  rw [cylinderPartialGrowth, cylinderPartialD, h1, h2, fderiv_mulCoord]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ne_eq, one_ne_zero,
    not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero]
end Malliavin
