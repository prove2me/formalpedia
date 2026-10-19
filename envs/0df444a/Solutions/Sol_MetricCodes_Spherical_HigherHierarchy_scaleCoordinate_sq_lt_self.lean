-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.scaleCoordinate_sq_lt_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/503aa11f-18f8-46a2-9aea-af73fd2e078a

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
    (hc : 0 < c) (hc' : c < 1) (hu : 0 < u) :
    scaleCoordinate (c ^ 2) u < u := by
  have hscale : 0 ≤ scaleCoordinate (c ^ 2) u :=
    scaleCoordinate_nonneg (sq_nonneg c) hu.le
  have hquad : 0 < quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  by_contra hnot
  have hle : u ≤ scaleCoordinate (c ^ 2) u := le_of_not_gt hnot
  have hmon := quadraticCoordinate_strictMonoOn.monotoneOn hu.le hscale hle
  rw [quadraticCoordinate_scaleCoordinate (sq_nonneg c) hu.le] at hmon
  nlinarith [mul_pos (sub_pos.mpr hc') (by linarith : 0 < 1 + c)]
end MetricCodes.Spherical.HigherHierarchy
