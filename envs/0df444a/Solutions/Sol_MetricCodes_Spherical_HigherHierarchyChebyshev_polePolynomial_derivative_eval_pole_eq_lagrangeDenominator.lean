-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_derivative_eval_pole_eq_lagrangeDenominator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/0f5e08a3-088a-4e76-b562-7d5306f93fb5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_quadraticCoordinate_ambient
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_polePolynomial_derivative_eval_pole

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
    {R : ℝ} (hR : 0 < R) (r : ℕ) (ℓ : Fin (r + 1)) :
    (polePolynomial R (r + 1)).derivative.eval
        (pole R (r + 1) ℓ.val) =
      MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator
        (ambient R r) ℓ := by
  rw [polePolynomial_derivative_eval_pole]
  unfold MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator
  apply Finset.prod_congr rfl
  intro m _hm
  rw [quadraticCoordinate_ambient hR r ℓ,
    quadraticCoordinate_ambient hR r (ℓ.succAbove m)]
end MetricCodes.Spherical.HigherHierarchyChebyshev
