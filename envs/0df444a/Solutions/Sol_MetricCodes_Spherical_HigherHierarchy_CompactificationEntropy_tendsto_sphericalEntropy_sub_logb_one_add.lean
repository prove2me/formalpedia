-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_sphericalEntropy_sub_logb_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/4e93e37a-bb03-4e47-a4f2-b989f62472d0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sphericalEntropy_eq_log_add

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
theorem _root_.solution :
    Tendsto (fun a : ℝ =>
      MetricCodes.sphericalEntropy a - Real.logb 2 (1 + a))
      atTop (𝓝 (1 / Real.log 2)) := by
  have hmain :=
    (Real.tendsto_mul_log_one_add_div_atTop 1).div_const (Real.log 2)
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [MetricCodes.sphericalEntropy_eq_log_add ha]
  have hratio : (1 + a) / a = 1 + 1 / a := by
    field_simp
    ring
  rw [hratio]
  unfold Real.logb
  ring
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
