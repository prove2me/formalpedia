-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.sqrt_degree_mul_one_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/e11e3a95-5dde-402c-961a-2f10afc29deb

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
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) :
    Real.sqrt (a * (1 + a)) = a * Real.sqrt (1 + a⁻¹) := by
  have hfactor : a * (1 + a) = a ^ 2 * (1 + a⁻¹) := by
    field_simp
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
