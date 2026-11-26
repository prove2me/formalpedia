-- Prove2me | solution 1 for Malliavin.exp_brownian_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:45.932353+00:00
-- url     : https://prove2.me/submissions/21707837-ca02-42c8-bdd9-17ed42a063cd

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_abs_deriv_exp_le_exp_abs
import Theorems.Thm_Malliavin_comp_brownian_mem_domD12

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
theorem _root_.solution (T : ℝ≥0) : (memLp_exp_brownian L hL T).toLp _ ∈ domD12 P :=
  comp_brownian_mem_domD12 L hL Real.contDiff_exp zero_le_one zero_le_one abs_exp_le_exp_abs
    abs_deriv_exp_le_exp_abs T
end Malliavin
