-- Prove2me | solution 1 for Malliavin.cylinder_growth_brownian_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:32:32.320435+00:00
-- url     : https://prove2.me/submissions/2b5d3c20-e775-465c-af26-891562a52e00

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_growth_truncCoord_le
import Theorems.Thm_Malliavin_cylinder_brownian_mem_domD12_of_dominated

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
theorem _root_.solution {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialGrowth L hL hf hC hfg' t i) :=
  cylinder_brownian_mem_domD12_of_dominated L hL hf hfg hfg' t (growth_truncCoord_le hC _)
    (growth_coord_le hC _) (integrable_growth_sq P C _)
end Malliavin
