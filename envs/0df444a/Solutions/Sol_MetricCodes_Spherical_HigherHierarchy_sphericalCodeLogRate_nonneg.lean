-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sphericalCodeLogRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/b874562c-275a-40fa-9aa0-342be39aea1f

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution (s : ℝ) (n : ℕ) :
    0 ≤ Real.logb 2
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ) := by
  apply div_nonneg _ (Nat.cast_nonneg n)
  cases hcard : (SpherePacking.sphericalCodeNumber n s).toNat with
  | zero => simp
  | succ k =>
      apply Real.logb_nonneg (by norm_num)
      exact_mod_cast Nat.succ_pos k
end MetricCodes.Spherical.HigherHierarchy
