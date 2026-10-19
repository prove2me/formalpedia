-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.scaleCoordinate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/aad9f5ee-a787-4761-a712-55ec204e8ab4

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
theorem _root_.solution {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    0 < scaleCoordinate c u := by
  simpa using scaleCoordinate_strictMonoOn hc
    (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show u ∈ Set.Ici 0 from hu.le) hu
end MetricCodes.Spherical.HigherHierarchy
