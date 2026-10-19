-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/b9e56805-7c8a-4d8b-9338-4c038e62d2fa

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
    (stabilizerPolynomial b).natDegree = r := by
  simp [stabilizerPolynomial,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
end MetricCodes.Spherical.HigherHierarchy
