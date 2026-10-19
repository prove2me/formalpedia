-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_sphericalEntropy_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/efdd7952-b1d3-41e3-9443-b20db9554cf1

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
theorem _root_.solution :
    Tendsto (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2) / t)
      (𝓝[>] 0) (nhds 0) := by
  let f : ℝ → ℝ := fun t =>
    (1 + t ^ 2) * Real.logb 2 (1 + t ^ 2)
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).fun_pow 2
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) 0 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_add hsquare
  have hlog : HasDerivAt (fun t : ℝ => Real.logb 2 (1 + t ^ 2)) 0 0 := by
    unfold Real.logb
    have hlogbase : HasDerivAt Real.log 1 (1 + (0 : ℝ) ^ 2) := by
      simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
    have hnatural := hlogbase.comp 0 hinner
    simpa [Function.comp_def] using hnatural.div_const (Real.log 2)
  have hf : HasDerivAt f 0 0 := by
    dsimp [f]
    simpa using hinner.fun_mul hlog
  have hfirst : Tendsto (fun t : ℝ => f t / t)
      (𝓝[>] 0) (nhds 0) := by
    have hslope := hf.tendsto_slope_zero_right
    simpa [f, div_eq_mul_inv, mul_comm, smul_eq_mul] using hslope
  have hsecond : Tendsto (fun t : ℝ => 2 * (t * Real.logb 2 t))
      (𝓝[>] 0) (nhds 0) := by
    have hnatural := Real.continuous_mul_log.continuousAt
      (x := (0 : ℝ))
    have hbase : Tendsto (fun t : ℝ => t * Real.logb 2 t)
        (𝓝[>] 0) (nhds 0) := by
      unfold Real.logb
      have h : Tendsto (fun t : ℝ => (t * Real.log t) / Real.log 2)
          (nhds (0 : ℝ)) (nhds 0) := by
        simpa using hnatural.tendsto.div_const (Real.log 2)
      simpa [div_eq_mul_inv, mul_assoc] using
        h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    convert hbase.const_mul 2 using 1; simp
  have heq : (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2) / t)
      =ᶠ[𝓝[>] 0] (fun t => f t / t - 2 * (t * Real.logb 2 t)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    unfold MetricCodes.sphericalEntropy
    rw [Real.logb_pow]
    dsimp [f]
    field_simp [ht.ne']
  simpa using (hfirst.sub hsecond).congr' heq.symm
end MetricCodes.Spherical.HigherHierarchy
