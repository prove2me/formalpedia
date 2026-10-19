-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_eq_fin_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/2075f2d8-284b-4760-882a-6d85eac0c9ca

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
theorem _root_.solution (R : ℝ) (r : ℕ) :
    polePolynomial R (r + 1) =
      ∏ i : Fin (r + 1),
        (Polynomial.X - Polynomial.C (pole R (r + 1) i.val)) := by
  unfold polePolynomial
  exact (Fin.prod_univ_eq_prod_range
    (fun i => Polynomial.X - Polynomial.C (pole R (r + 1) i))
    (r + 1)).symm
end MetricCodes.Spherical.HigherHierarchyChebyshev
