-- Prove2me | solution 1 for Malliavin.comp_brownian_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:19.540099+00:00
-- url     : https://prove2.me/submissions/5f29d3c7-f263-4cc7-817d-9bfb0abf0eb3

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_cylinder_expGrowth_brownian_mem_domD12

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
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|))
    (T : ℝ≥0) : (memLp_comp_brownian L hL hg hC hc hgb T).toLp _ ∈ domD12 P :=
  (cylinder_expGrowth_brownian_mem_domD12 L hL (contDiff_oneCoord hg) hC hc
    (abs_oneCoord_le hC hc hgb) (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T)).1
end Malliavin
