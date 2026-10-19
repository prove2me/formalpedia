-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.quadratic_residue_ratio_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/d79845f6-0bac-4a41-b65c-6f1be41d48b4

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
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (x u v : ℝ) (hu : u ≠ 0) :
    (x - quadraticCoordinate v) / (x - quadraticCoordinate u) =
      (x * (u⁻¹) ^ 2 - (v / u) ^ 2 - (v / u) * u⁻¹) /
        (x * (u⁻¹) ^ 2 - 1 - u⁻¹) := by
  unfold quadraticCoordinate
  field_simp [hu]
  ring
end MetricCodes.Spherical.HigherHierarchy
