-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator_prepend_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/27c90ee2-945c-4316-90d0-c7b9f634af00

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
    (a : Fin (r + 1) → ℝ) (u : ℝ) (i : Fin (r + 1)) :
    lagrangeDenominator (prependAmbient u a) i.succ =
      (quadraticCoordinate (a i) - quadraticCoordinate u) *
        lagrangeDenominator a i := by
  simp [lagrangeDenominator, prependAmbient, Fin.prod_univ_succ]
end MetricCodes.Spherical.HigherHierarchy
