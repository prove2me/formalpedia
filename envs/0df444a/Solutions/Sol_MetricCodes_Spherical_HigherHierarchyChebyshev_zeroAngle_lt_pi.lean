-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.zeroAngle_lt_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/e0f7ded2-065d-4bca-a74c-944511a4a523

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
theorem _root_.solution {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    zeroAngle N j < Real.pi := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj' : (j : ℝ) < (N : ℝ) := by exact_mod_cast hj
  unfold zeroAngle
  apply (div_lt_iff₀ hN').2
  nlinarith [mul_lt_mul_of_pos_right hj' Real.pi_pos]
end MetricCodes.Spherical.HigherHierarchyChebyshev
