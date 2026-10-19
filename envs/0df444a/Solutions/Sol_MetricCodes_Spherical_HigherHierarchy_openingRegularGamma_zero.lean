-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.openingRegularGamma_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/dc4a974a-deb2-4bb3-9c79-5f85948fd1a7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_opening_eq_regular_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (hzero : a (Fin.last r) = 0) (η : ℝ) :
    openingRegularGamma a b η 0 = Gamma a b := by
  have hsplit := Gamma_opening_eq_regular_add a b η 0
  simpa [openingAmbient_zero hzero, spectralAtom, quadraticCoordinate] using
    hsplit.symm
end MetricCodes.Spherical.HigherHierarchy
