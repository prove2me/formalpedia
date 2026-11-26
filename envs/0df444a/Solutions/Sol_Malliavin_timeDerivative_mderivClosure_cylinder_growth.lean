-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_cylinder_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:32:30.657226+00:00
-- url     : https://prove2.me/submissions/20692bce-e64c-4399-b559-042c5448cb75

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_growth_truncCoord_le
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_cylinder_of_dominated

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
theorem _root_.solution (hgen : IsWienerGenerated B) {n k : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialGrowth L hL hf hC hfg' t i) :=
  timeDerivative_mderivClosure_cylinder_of_dominated hB L hL hgen hf hfg hfg' t
    (growth_truncCoord_le hC _) (growth_coord_le hC _) (integrable_growth_sq P C _)
end Malliavin
