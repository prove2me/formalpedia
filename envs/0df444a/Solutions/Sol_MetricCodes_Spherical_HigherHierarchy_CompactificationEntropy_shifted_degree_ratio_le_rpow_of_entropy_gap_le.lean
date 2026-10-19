-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.shifted_degree_ratio_le_rpow_of_entropy_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/4893e6f3-1a48-4ee3-b4d9-99f8ae7d24d4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_upper_logb_add
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
    {a b C : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hC : MetricCodes.sphericalEntropy a -
      MetricCodes.sphericalEntropy b ≤ C) :
    (1 + a) / (1 + b) ≤
      (2 : ℝ) ^ (C + 1 / Real.log 2) := by
  have ha : 0 < a := hb.trans_le hba
  have hlower := logb_one_add_le_sphericalEntropy ha.le
  have hupper :=
    MetricCodes.Spherical.sphericalEntropy_upper_logb_add hb
  have hlog :
      Real.logb 2 (1 + a) - Real.logb 2 (1 + b) ≤
        C + 1 / Real.log 2 := by
    linarith
  have hratio :
      Real.logb 2 ((1 + a) / (1 + b)) ≤
        C + 1 / Real.log 2 := by
    rw [Real.logb_div (by positivity) (by positivity)]
    exact hlog
  exact (Real.logb_le_iff_le_rpow
    (by norm_num : (1 : ℝ) < 2) (by positivity)).mp hratio
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
