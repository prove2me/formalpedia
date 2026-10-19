-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.zeroAngle_lt_poleAngle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/1e22a91b-c704-4713-bf6f-7f230498beba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_eq_midpoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {N i : ℕ} (hN : 0 < N) :
    zeroAngle N i < poleAngle N i := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [poleAngle_eq_midpoint hN]
  unfold zeroAngle
  apply (div_lt_div_iff_of_pos_right hN').2
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
end MetricCodes.Spherical.HigherHierarchyChebyshev
