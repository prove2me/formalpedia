-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_derivative_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/f4ee5a6a-8b0c-453f-9a27-ff15c3db339e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_eq_leadingCoeff_mul_polePolynomial
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_derivative_eval_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_shiftedChebyshev_leadingCoeff_ne_zero

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
    {N j : ℕ} (hjpos : 0 < j) (hj : j < N) :
    (polePolynomial R N).derivative.eval (zero R N j) = 0 := by
  have hN : 0 < N := hjpos.trans hj
  have heq := congrArg Polynomial.derivative
    (shiftedChebyshev_eq_leadingCoeff_mul_polePolynomial hR N)
  have hev := congrArg (Polynomial.eval (zero R N j)) heq
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, Polynomial.eval_mul, Polynomial.eval_C, zero_add] at hev
  rw [shiftedChebyshev_derivative_eval_zero hR hjpos hj] at hev
  exact (mul_eq_zero.mp hev.symm).resolve_left
    (shiftedChebyshev_leadingCoeff_ne_zero hR hN)
end MetricCodes.Spherical.HigherHierarchyChebyshev
