-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.poleAngle_lt_succ_zeroAngle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/1a3640e4-0d20-425a-a9f2-ee19e68ee9ff

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
    poleAngle N i < zeroAngle N (i + 1) := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [poleAngle_eq_midpoint hN]
  unfold zeroAngle
  push_cast
  apply (div_lt_div_iff_of_pos_right hN').2
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
end MetricCodes.Spherical.HigherHierarchyChebyshev
