-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a4146c5f-078b-4f4c-bbe5-182536180117

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
theorem _root_.solution {r : ℕ} (b : Fin r → ℝ) :
    (stabilizerPolynomial b).Monic := by
  exact Polynomial.monic_prod_X_sub_C
    (fun m : Fin r => quadraticCoordinate (b m)) Finset.univ
end MetricCodes.Spherical.HigherHierarchy
