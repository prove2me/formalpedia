-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.le_scaleCoordinate_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/e71a6ddf-f689-437e-89c5-92bf9df9263d

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
theorem _root_.solution {c u : ℝ}
    (hc : 1 ≤ c) (hu : 0 ≤ u) : u ≤ scaleCoordinate c u := by
  have hquad : quadraticCoordinate u ≤
      quadraticCoordinate (scaleCoordinate c u) := by
    rw [quadraticCoordinate_scaleCoordinate (by linarith) hu]
    have hx : 0 ≤ quadraticCoordinate u := by
      unfold quadraticCoordinate
      positivity
    nlinarith
  by_contra hnot
  have hreverse : scaleCoordinate c u < u := lt_of_not_ge hnot
  exact (not_le_of_gt
    (quadraticCoordinate_strictMonoOn
      (scaleCoordinate_nonneg (by linarith) hu) hu hreverse)) hquad
end MetricCodes.Spherical.HigherHierarchy
