-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.spectralAtom_scale_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/d19502d8-6c3d-481b-8003-151919121917

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_strictMonoOn

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
theorem _root_.solution {c u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    spectralAtom u < spectralAtom (scaleCoordinate c u) := by
  have hquad : quadraticCoordinate u <
      quadraticCoordinate (scaleCoordinate c u) := by
    rw [quadraticCoordinate_scaleCoordinate (by linarith) hu.le]
    have hx : 0 < quadraticCoordinate u := by
      unfold quadraticCoordinate
      positivity
    nlinarith
  have hcoord : u < scaleCoordinate c u := by
    by_contra hnot
    have hrev : scaleCoordinate c u ≤ u := le_of_not_gt hnot
    exact (not_le_of_gt hquad)
      (quadraticCoordinate_strictMonoOn.monotoneOn
        (scaleCoordinate_nonneg (by linarith) hu.le) hu.le hrev)
  exact spectralAtom_strictMonoOn hu.le
    (scaleCoordinate_nonneg (by linarith) hu.le) hcoord
end MetricCodes.Spherical.HigherHierarchy
