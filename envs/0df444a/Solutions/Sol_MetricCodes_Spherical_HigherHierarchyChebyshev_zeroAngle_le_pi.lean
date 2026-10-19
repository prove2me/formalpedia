-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.zeroAngle_le_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/6db22f72-232d-4602-b680-a4b5ee17c979

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    zeroAngle N j ≤ Real.pi := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj' : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
  unfold zeroAngle
  apply (div_le_iff₀ hN').2
  nlinarith [mul_le_mul_of_nonneg_right hj' Real.pi_pos.le]
end MetricCodes.Spherical.HigherHierarchyChebyshev
