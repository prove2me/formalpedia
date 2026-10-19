-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_derivative_eval_pole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/d30a9450-5f90-45d7-9482-ecabab2a7a90

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_eq_fin_prod

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution
    (R : ℝ) (r : ℕ) (ℓ : Fin (r + 1)) :
    (polePolynomial R (r + 1)).derivative.eval
        (pole R (r + 1) ℓ.val) =
      ∏ m : Fin r,
        (pole R (r + 1) ℓ.val -
          pole R (r + 1) (ℓ.succAbove m).val) := by
  rw [polePolynomial_eq_fin_prod,
    Fin.prod_univ_succAbove
      (fun i : Fin (r + 1) =>
        Polynomial.X - Polynomial.C (pole R (r + 1) i.val)) ℓ]
  simp [Polynomial.derivative_mul, Polynomial.eval_prod]
end MetricCodes.Spherical.HigherHierarchyChebyshev
