-- Prove2me | solution 1 for Malliavin.growth_truncCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:31:19.095422+00:00
-- url     : https://prove2.me/submissions/b7a9370b-852f-43d0-83ec-da02133f01f8

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_norm_truncCoord_le_norm

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution {n k : ℕ} {C : ℝ} (hC : 0 ≤ C) (L : Fin n → StrongDual ℝ W)
    (m : ℕ) (x : W) :
    C * (1 + ‖truncCoord m L x‖) ^ k ≤ C * gaussWeight L x ^ k := by
  gcongr
  exact (add_le_add_right (norm_truncCoord_le_norm m L x) 1).trans
    (one_add_norm_le_gaussWeight L x)
end Malliavin
