-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.boundaryDegree_div_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/870bd65c-ba0a-4c40-9e8e-723c6a37e87d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_boundaryQuadratic_eq_sq_mul_normalized

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
    {s a : ℝ} (ha : 0 < a) :
    MetricCodes.Spherical.boundaryDegree s a / a =
      normalizedBoundaryDegree s a⁻¹ := by
  have hfactor :
      1 + 4 * MetricCodes.Spherical.boundaryQuadratic s a =
        a ^ 2 *
          (a⁻¹ ^ 2 + 4 * normalizedBoundaryQuadratic s a⁻¹) := by
    rw [boundaryQuadratic_eq_sq_mul_normalized ha]
    field_simp
  unfold MetricCodes.Spherical.boundaryDegree normalizedBoundaryDegree
  rw [hfactor, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  field_simp
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
