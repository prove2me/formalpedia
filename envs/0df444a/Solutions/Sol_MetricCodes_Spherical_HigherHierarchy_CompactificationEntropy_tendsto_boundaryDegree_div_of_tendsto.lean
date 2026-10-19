-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_boundaryDegree_div_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/993ebddc-9b0b-448b-9686-78b22c6f8c4a

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
open Filter Topology
open scoped Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution
    {u a : ℕ → ℝ} {s : ℝ}
    (hu : Tendsto u atTop (𝓝 s))
    (ha : Tendsto a atTop atTop) :
    Tendsto
      (fun n => MetricCodes.Spherical.boundaryDegree (u n) (a n) / a n)
      atTop (𝓝 (Real.sqrt (1 - s))) := by
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ha
  have hcontinuous : Continuous (fun p : ℝ × ℝ =>
      normalizedBoundaryDegree p.1 p.2) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    fun_prop
  have hzero : normalizedBoundaryDegree s 0 = Real.sqrt (1 - s) := by
    unfold normalizedBoundaryDegree normalizedBoundaryQuadratic
    have hfactor : (0 : ℝ) ^ 2 +
        4 * (1 + 0 - (s / 2) * (0 + 2) * Real.sqrt (1 + 0)) =
          4 * (1 - s) := by
      norm_num
    rw [hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hlimit := hcontinuous.continuousAt.tendsto.comp (hu.prodMk_nhds hinv)
  change Tendsto (fun n => normalizedBoundaryDegree (u n) (a n)⁻¹)
    atTop (𝓝 (normalizedBoundaryDegree s 0)) at hlimit
  rw [hzero] at hlimit
  apply hlimit.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  exact (boundaryDegree_div_eq_normalized hn).symm
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
