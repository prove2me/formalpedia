-- Prove2me | solution 1 for Malliavin.polynomial_brownian_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:58.237055+00:00
-- url     : https://prove2.me/submissions/044392b7-704a-4e41-9f48-761f169a02d4

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
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
theorem _root_.solution (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian L hL p T).toLp _ ∈ domD12 P :=
  comp_brownian_mem_domD12 L hL (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) (abs_polynomial_deriv_le' p) T
end Malliavin
