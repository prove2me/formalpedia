-- Prove2me | solution 1 for Malliavin.norm_truncCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:34.897864+00:00
-- url     : https://prove2.me/submissions/987d1817-24b3-4226-a827-a5b31be98213

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_abs_cutoff_le_const


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Malliavin
theorem _root_.solution (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖truncCoord m L x‖ ≤ (m + 1) * (Real.pi / 2) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_cutoff_le_const m _
end Malliavin
