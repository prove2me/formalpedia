-- Prove2me | solution 1 for Malliavin.abs_cos_le_exp_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:38.264567+00:00
-- url     : https://prove2.me/submissions/b55499c5-3d05-4494-965e-a41424ca928e

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {g : ℝ → ℝ}
namespace Malliavin
theorem _root_.solution (x : ℝ) : |Real.cos x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [one_mul, one_mul]
  exact (Real.abs_cos_le_one x).trans (Real.one_le_exp (abs_nonneg x))
end Malliavin
