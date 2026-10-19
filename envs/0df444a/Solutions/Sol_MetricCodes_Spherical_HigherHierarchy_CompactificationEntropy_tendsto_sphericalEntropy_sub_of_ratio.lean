-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_sphericalEntropy_sub_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/945c3727-1dd2-48c6-8f2e-92a5f514ab0e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_sphericalEntropy_sub_logb_one_add

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
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f atTop atTop)
    (hratio : Tendsto (fun a : ℝ => f a / a) atTop (𝓝 c)) :
    Tendsto (fun a : ℝ =>
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy (f a))
      atTop (𝓝 (-Real.logb 2 c)) := by
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hnormalized :
      Tendsto (fun a : ℝ =>
        (a⁻¹ + f a / a) / (a⁻¹ + 1)) atTop (𝓝 c) := by
    convert (hinv.add hratio).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext a
      rfl
    · norm_num
  have hshifted :
      Tendsto (fun a : ℝ => (1 + f a) / (1 + a))
        atTop (𝓝 c) := by
    apply hnormalized.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    field_simp
  have hlog : Tendsto
      (fun a : ℝ => Real.logb 2 ((1 + f a) / (1 + a)))
        atTop (𝓝 (Real.logb 2 c)) :=
    (Real.continuousAt_logb hc.ne').tendsto.comp hshifted
  have hfirst := tendsto_sphericalEntropy_sub_logb_one_add
  have hsecond := tendsto_sphericalEntropy_sub_logb_one_add.comp hf
  have hlimit := (hfirst.sub hsecond).sub hlog
  have htarget :
      (1 / Real.log 2 - 1 / Real.log 2) - Real.logb 2 c =
        -Real.logb 2 c := by ring
  rw [htarget] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_gt_atTop (0 : ℝ))] with a ha hfa
  rw [Real.logb_div (by positivity) (by positivity)]
  simp only [Function.comp_apply]
  ring
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
