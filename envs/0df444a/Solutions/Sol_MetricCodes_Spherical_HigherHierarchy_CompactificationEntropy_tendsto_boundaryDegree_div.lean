-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_boundaryDegree_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/7ab46181-ba07-455a-b70d-71b0e0acb71f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_boundaryDegree_div_eq_normalized

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
    {s : ℝ} (hs : s < 1) :
    Tendsto
      (fun a : ℝ => MetricCodes.Spherical.boundaryDegree s a / a)
      atTop (𝓝 (Real.sqrt (1 - s))) := by
  have hcontinuous : Continuous (fun u : ℝ =>
      normalizedBoundaryDegree s u) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    fun_prop
  have hzero : normalizedBoundaryDegree s 0 =
      Real.sqrt (1 - s) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    have hfactor : (0 : ℝ) ^ 2 +
        4 * (1 + 0 - (s / 2) * (0 + 2) * Real.sqrt (1 + 0)) =
          4 * (1 - s) := by
      norm_num
    rw [hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hlimit := hcontinuous.continuousAt.tendsto.comp hinv
  rw [hzero] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (boundaryDegree_div_eq_normalized ha).symm
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
