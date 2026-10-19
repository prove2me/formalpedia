-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.zero_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/d133890e-7abf-4d61-914b-81d3aeb1024c

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
theorem _root_.solution {R : ℝ} (hR : 0 ≤ R) (N j : ℕ) :
    0 ≤ zero R N j := by
  unfold zero
  exact mul_nonneg (by positivity)
    (by linarith [Real.neg_one_le_cos (zeroAngle N j)])
end MetricCodes.Spherical.HigherHierarchyChebyshev
