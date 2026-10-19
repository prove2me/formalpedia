-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.degree_le_rpow_sub_one_of_sphericalEntropy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/d9a5c101-9fec-4ab4-8d81-69421da9f5aa

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_logb_one_add_le_sphericalEntropy

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
    {u C : ℝ} (hu : 0 ≤ u)
    (hC : MetricCodes.sphericalEntropy u ≤ C) :
    u ≤ (2 : ℝ) ^ C - 1 := by
  have hlog : Real.logb 2 (1 + u) ≤ C :=
    (logb_one_add_le_sphericalEntropy hu).trans hC
  have hpow : 1 + u ≤ (2 : ℝ) ^ C :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by linarith : 0 < 1 + u)).mp hlog
  linarith
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
