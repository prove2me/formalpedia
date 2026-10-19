-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactified_zero_residual_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/3d2e257d-ea59-49f1-916a-7358caeabf29

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s c : ℝ} (_hs : 0 < s) (_hs' : s < 1)
    (hc : 0 < c) (hfeasible : s ≤ 1 - c ^ 2) :
    -(1 / 2 : ℝ) * Real.logb 2 (1 - s) ≤ -Real.logb 2 c := by
  have hcsquare : 0 < c ^ 2 := sq_pos_of_pos hc
  have hsquare : c ^ 2 ≤ 1 - s := by linarith
  have hlog : Real.logb 2 (c ^ 2) ≤ Real.logb 2 (1 - s) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      hcsquare hsquare
  rw [Real.logb_pow] at hlog
  norm_num at hlog ⊢
  linarith
end MetricCodes.Spherical.HigherHierarchy
