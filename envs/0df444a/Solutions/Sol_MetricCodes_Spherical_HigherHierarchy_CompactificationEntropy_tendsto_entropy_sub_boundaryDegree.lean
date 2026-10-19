-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_entropy_sub_boundaryDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/6d0d99d0-dfe0-41d7-80fa-169be17289ce

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_sphericalEntropy_sub_of_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_boundaryDegree_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_boundaryDegree_atTop

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    Tendsto (fun a : ℝ =>
      MetricCodes.sphericalEntropy a -
        MetricCodes.sphericalEntropy
          (MetricCodes.Spherical.boundaryDegree s a))
      atTop (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (1 - s))) := by
  have hroot : 0 < Real.sqrt (1 - s) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hs')
  have hlimit := tendsto_sphericalEntropy_sub_of_ratio hroot
    (tendsto_boundaryDegree_atTop hs') (tendsto_boundaryDegree_div hs')
  have hconstant :
      -Real.logb 2 (Real.sqrt (1 - s)) =
        -(1 / 2 : ℝ) * Real.logb 2 (1 - s) := by
    unfold Real.logb
    rw [Real.log_sqrt (sub_pos.mpr hs').le]
    ring
  rw [hconstant] at hlimit
  exact hlimit
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
