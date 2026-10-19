-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.affinePolynomial_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/94821c30-80e9-4720-a2b3-bab4f94011a6

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
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    (N j : ℕ) :
    (affinePolynomial R).eval (zero R N j) =
      Real.cos (zeroAngle N j) := by
  have hR' : R ≠ 0 := hR.ne'
  simp [affinePolynomial, zero]
  field_simp
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
