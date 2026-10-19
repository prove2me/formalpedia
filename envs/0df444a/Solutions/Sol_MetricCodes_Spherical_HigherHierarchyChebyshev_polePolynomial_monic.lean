-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/82c21d25-f59a-4606-b677-111b26051d0b

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
    (polePolynomial R N).Monic := by
  unfold polePolynomial
  exact Polynomial.monic_prod_of_monic _ _
    (fun i _hi => Polynomial.monic_X_sub_C (pole R N i))
end MetricCodes.Spherical.HigherHierarchyChebyshev
