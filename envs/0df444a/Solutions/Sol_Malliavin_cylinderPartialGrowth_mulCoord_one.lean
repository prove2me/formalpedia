-- Prove2me | solution 1 for Malliavin.cylinderPartialGrowth_mulCoord_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:05.236501+00:00
-- url     : https://prove2.me/submissions/b5f06131-cb03-4903-903b-73531373f118

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
        ![S, T] 1 = (memLp_brownian L hL S).toLp _ := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL contDiff_mulCoord
      norm_fderiv_mulCoord_le ![S, T] (growth_coord_le zero_le_two _)
      (integrable_growth_sq P 2 _) 1),
    MemLp.coeFn_toLp (memLp_brownian L hL S)] with w h1 h2
  rw [cylinderPartialGrowth, cylinderPartialD, h1, h2, fderiv_mulCoord]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul,
    mul_zero, Pi.single_eq_same, mul_one, zero_add]
end Malliavin
