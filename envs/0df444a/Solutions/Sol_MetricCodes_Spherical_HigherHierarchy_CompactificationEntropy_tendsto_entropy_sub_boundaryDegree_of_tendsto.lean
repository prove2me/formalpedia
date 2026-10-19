-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_entropy_sub_boundaryDegree_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/ff073efa-3381-4b69-947c-416eedf2c088

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_boundaryDegree_div_of_tendsto
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_boundaryDegree_atTop_of_tendsto
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_sphericalEntropy_sub_of_sequential_ratio

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
    {u a : ℕ → ℝ} {s : ℝ} (_hs : 0 < s) (hs' : s < 1)
    (hu : Tendsto u atTop (𝓝 s))
    (ha : Tendsto a atTop atTop) :
    Tendsto (fun n =>
      MetricCodes.sphericalEntropy (a n) -
        MetricCodes.sphericalEntropy
          (MetricCodes.Spherical.boundaryDegree (u n) (a n)))
      atTop (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (1 - s))) := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs')
  have hratio := tendsto_boundaryDegree_div_of_tendsto hu ha
  have hboundary := tendsto_boundaryDegree_atTop_of_tendsto hs' hu ha
  have hlimit := tendsto_sphericalEntropy_sub_of_sequential_ratio
    hroot ha hboundary hratio
  have hconstant :
      -Real.logb 2 (Real.sqrt (1 - s)) =
        -(1 / 2 : ℝ) * Real.logb 2 (1 - s) := by
    unfold Real.logb
    rw [Real.log_sqrt (sub_pos.mpr hs').le]
    ring
  rwa [hconstant] at hlimit
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
