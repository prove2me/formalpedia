-- Prove2me | solution 1 for Malliavin.norm_truncCoord_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:35:22.997658+00:00
-- url     : https://prove2.me/submissions/ac96ecc0-d149-4314-bb6b-1347dfd78968

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_abs_cutoff_le


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
namespace Malliavin
theorem _root_.solution (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖truncCoord m L x‖ ≤ ‖fun i ↦ L i x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_cutoff_le m _).trans (norm_le_pi_norm (fun i ↦ L i x) i)
end Malliavin
