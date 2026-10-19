-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.boundaryQuadratic_eq_sq_mul_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/7a39a86f-7c99-44b4-afd8-1c55da486487

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_sqrt_degree_mul_one_add_eq

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
    MetricCodes.Spherical.boundaryQuadratic s a =
      a ^ 2 * normalizedBoundaryQuadratic s a⁻¹ := by
  unfold MetricCodes.Spherical.boundaryQuadratic
    normalizedBoundaryQuadratic
  rw [sqrt_degree_mul_one_add_eq ha]
  field_simp
  ring
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
