-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.normalizedDerivative_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/9954571e-6493-4a55-87bb-ae59bdbae91d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
    (normalizedDerivative R r).natDegree = r := by
  unfold normalizedDerivative
  have hN : ((r + 1 : ℕ) : ℝ)⁻¹ ≠ 0 := by positivity
  rw [Polynomial.natDegree_C_mul hN, Polynomial.natDegree_derivative,
    polePolynomial_natDegree]
  omega
end MetricCodes.Spherical.HigherHierarchyChebyshev
