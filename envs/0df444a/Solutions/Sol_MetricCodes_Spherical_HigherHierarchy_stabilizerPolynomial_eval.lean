-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/8f3b377e-e2bf-498b-9205-c6bf6c21c122

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) :
    (stabilizerPolynomial b).eval (quadraticCoordinate (a ℓ)) =
      lagrangeNumerator a b ℓ := by
  unfold stabilizerPolynomial lagrangeNumerator
  rw [Polynomial.eval_prod]
  simp
end MetricCodes.Spherical.HigherHierarchy
