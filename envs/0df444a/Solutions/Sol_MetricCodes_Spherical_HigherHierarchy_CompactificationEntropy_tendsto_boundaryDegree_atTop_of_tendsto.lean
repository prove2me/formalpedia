-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_boundaryDegree_atTop_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/6abd77e7-b722-49cc-85bb-86ad06f535ca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_boundaryDegree_div_of_tendsto

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
open scoped Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution
    {u a : ℕ → ℝ} {s : ℝ} (hs : s < 1)
    (hu : Tendsto u atTop (𝓝 s))
    (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => MetricCodes.Spherical.boundaryDegree (u n) (a n))
      atTop atTop := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs)
  have hratio := tendsto_boundaryDegree_div_of_tendsto hu ha
  have hproduct := ha.atTop_mul_pos hroot hratio
  apply hproduct.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  field_simp
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
