-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.normalizedDerivative_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/e27b558d-8e0a-4c2d-b984-c9a820cc3a33

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_monic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_natDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution (R : ℝ) (r : ℕ) :
    (normalizedDerivative R r).Monic := by
  unfold normalizedDerivative
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff_derivative, polePolynomial_natDegree,
    (polePolynomial_monic R (r + 1)).leadingCoeff]
  have hN : (r : ℝ) + 1 ≠ 0 := by positivity
  simpa using inv_mul_cancel₀ hN
end MetricCodes.Spherical.HigherHierarchyChebyshev
