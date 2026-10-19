-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_boundaryDegree_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/ed4cbbaf-8cb6-4e91-b5dd-2c81d1085226

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_boundaryDegree_div

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
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution
    {s : ℝ} (hs : s < 1) :
    Tendsto (MetricCodes.Spherical.boundaryDegree s) atTop atTop := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs)
  have hproduct := tendsto_id.atTop_mul_pos hroot
    (tendsto_boundaryDegree_div hs)
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  field_simp
  simp [mul_comm]
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
