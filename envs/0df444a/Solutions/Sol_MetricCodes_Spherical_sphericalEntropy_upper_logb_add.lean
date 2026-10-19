-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalEntropy_upper_logb_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/e86be711-3371-40f4-89c9-9cbe00e7d12a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_eq_logb_add_mul_logb

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
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) :
    MetricCodes.sphericalEntropy a ≤
      Real.logb 2 (1 + a) + 1 / Real.log 2 := by
  rw [sphericalEntropy_eq_logb_add_mul_logb ha]
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < (1 + a) / a by positivity)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hone : a * (((1 + a) / a) - 1) = 1 := by
    field_simp
    ring
  have hupper : a * Real.log ((1 + a) / a) ≤ 1 := by
    calc
      a * Real.log ((1 + a) / a) ≤
          a * (((1 + a) / a) - 1) :=
        mul_le_mul_of_nonneg_left hlog ha.le
      _ = 1 := hone
  unfold Real.logb
  have hfraction :
      a * (Real.log ((1 + a) / a) / Real.log 2) ≤
        1 / Real.log 2 := by
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hlogtwo).mpr hupper
  linarith
end MetricCodes.Spherical
