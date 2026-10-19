-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_opening_entropy_slope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/23b8e89d-49ac-495b-bdc9-741156d08641

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_hasDerivAt_sphericalEntropy
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_sphericalEntropy_sq_div

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
theorem _root_.solution {a η : ℝ}
    (ha : 0 < a) :
    Tendsto
      (fun t : ℝ =>
        (MetricCodes.sphericalEntropy (a - η * t) -
          MetricCodes.sphericalEntropy a +
          MetricCodes.sphericalEntropy (t ^ 2)) / t)
      (𝓝[>] 0)
      (nhds (-(η * Real.logb 2 ((1 + a) / a)))) := by
  have hlinear : HasDerivAt (fun t : ℝ => a - η * t) (-η) 0 := by
    simpa [mul_comm] using
      (hasDerivAt_const (0 : ℝ) a).fun_sub
        ((hasDerivAt_id (0 : ℝ)).const_mul η)
  have hbase : HasDerivAt MetricCodes.sphericalEntropy
      (Real.logb 2 ((1 + a) / a)) (a - η * (0 : ℝ)) := by
    simpa using MetricCodes.Spherical.hasDerivAt_sphericalEntropy ha
  have houter := hbase.comp 0 hlinear
  have hfirst : Tendsto
      (fun t : ℝ =>
        (MetricCodes.sphericalEntropy (a - η * t) -
          MetricCodes.sphericalEntropy a) / t)
      (𝓝[>] 0)
      (nhds (-(η * Real.logb 2 ((1 + a) / a)))) := by
    convert houter.tendsto_slope_zero_right using 1 <;>
      simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  have h := hfirst.add tendsto_sphericalEntropy_sq_div
  convert h using 1 <;> simp [add_div]
end MetricCodes.Spherical.HigherHierarchy
