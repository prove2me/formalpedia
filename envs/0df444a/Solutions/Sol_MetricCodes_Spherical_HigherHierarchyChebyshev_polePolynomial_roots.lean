-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/27246862-7d5e-497c-97a5-40873b748977

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
theorem _root_.solution (R : ℝ) (N : ℕ) :
    (polePolynomial R N).roots =
      (Finset.range N).val.map (pole R N) := by
  unfold polePolynomial
  rw [Polynomial.roots_prod]
  · simp
  · exact (Polynomial.monic_prod_X_sub_C (pole R N) (Finset.range N)).ne_zero
end MetricCodes.Spherical.HigherHierarchyChebyshev
