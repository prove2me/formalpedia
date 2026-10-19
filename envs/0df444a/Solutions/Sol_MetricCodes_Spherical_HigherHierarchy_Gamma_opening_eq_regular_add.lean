-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_opening_eq_regular_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/9ba59cc5-926d-4596-812f-f9e4a88188b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (η t : ℝ) :
    Gamma (openingAmbient a (η * t) (t ^ 2)) b =
      openingRegularGamma a b η t +
        lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b (Fin.last r) *
          spectralAtom (t ^ 2) := by
  unfold Gamma openingRegularGamma
  rw [Fin.sum_univ_castSucc]
  simp [openingAmbient]
end MetricCodes.Spherical.HigherHierarchy
