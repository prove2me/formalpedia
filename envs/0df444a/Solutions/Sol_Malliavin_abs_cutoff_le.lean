-- Prove2me | solution 1 for Malliavin.abs_cutoff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:11.945033+00:00
-- url     : https://prove2.me/submissions/de319e31-4547-4ed3-9de0-a1fa48420ef4

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_abs_arctan_le_abs

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ) (x : ℝ) : |cutoff n x| ≤ |x| := by
  unfold cutoff
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  calc (n + 1 : ℝ) * |Real.arctan (x / (n + 1))| ≤ (n + 1) * |x / (n + 1)| :=
        mul_le_mul_of_nonneg_left (abs_arctan_le_abs _) (by positivity)
    _ = |x| := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
          mul_div_cancel₀ _ (by positivity : (n + 1 : ℝ) ≠ 0)]
end Malliavin
