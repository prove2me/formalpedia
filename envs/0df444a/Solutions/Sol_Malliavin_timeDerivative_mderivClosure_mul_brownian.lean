-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_mul_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:33:32.530614+00:00
-- url     : https://prove2.me/submissions/95c1399d-a52b-4171-aa0d-29dd4fecb337

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cylinder_growth
import Theorems.Thm_Malliavin_cylinderPartialGrowth_mulCoord_zero
import Theorems.Thm_Malliavin_cylinderPartialGrowth_mulCoord_one

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
namespace Malliavin
theorem _root_.solution (hgen : IsWienerGenerated B) (S T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_mul_brownian L hL S T).toLp _)) =
      tensor (intervalIndicator S) ((memLp_brownian L hL T).toLp _) +
        tensor (intervalIndicator T) ((memLp_brownian L hL S).toLp _) := by
  have h := timeDerivative_mderivClosure_cylinder_growth hB L hL hgen contDiff_mulCoord
    zero_le_two abs_mulCoord_le norm_fderiv_mulCoord_le ![S, T]
  rw [Fin.sum_univ_two, cylinderPartialGrowth_mulCoord_zero, cylinderPartialGrowth_mulCoord_one]
    at h
  exact h
end Malliavin
