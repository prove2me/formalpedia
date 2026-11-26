-- Prove2me | solution 1 for Malliavin.abs_cutoff_le_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:14.007526+00:00
-- url     : https://prove2.me/submissions/dcd14f8e-ea68-49c2-b420-97aa4e51ee06

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ) (x : ℝ) : |cutoff n x| ≤ (n + 1) * (Real.pi / 2) := by
  unfold cutoff
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)
end Malliavin
