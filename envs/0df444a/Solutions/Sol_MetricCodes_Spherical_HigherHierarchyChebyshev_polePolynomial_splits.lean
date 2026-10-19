-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.polePolynomial_splits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/3c0f1226-e473-420f-8aef-cf244b051ece

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
    (polePolynomial R N).Splits := by
  unfold polePolynomial
  exact Polynomial.Splits.prod
    (fun i _hi => Polynomial.Splits.X_sub_C (pole R N i))
end MetricCodes.Spherical.HigherHierarchyChebyshev
