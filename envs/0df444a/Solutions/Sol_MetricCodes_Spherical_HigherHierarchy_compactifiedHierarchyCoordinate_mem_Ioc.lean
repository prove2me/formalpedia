-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedHierarchyCoordinate_mem_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/806fe421-a1b6-479d-9b4b-be4445c37984

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) :
    compactifiedHierarchyCoordinate u ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact inv_pos.mpr (by linarith)
  · exact (inv_le_one₀ (by linarith)).2 (by linarith)
end MetricCodes.Spherical.HigherHierarchy
