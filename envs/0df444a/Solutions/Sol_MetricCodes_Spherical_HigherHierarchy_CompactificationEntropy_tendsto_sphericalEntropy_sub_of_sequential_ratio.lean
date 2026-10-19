-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.tendsto_sphericalEntropy_sub_of_sequential_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/ef59716b-169b-4af1-968d-e881c85181ef

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
open Filter Topology
open scoped Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution
    {a b : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (ha : Tendsto a atTop atTop)
    (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun n => b n / a n) atTop (𝓝 c)) :
    Tendsto (fun n =>
      MetricCodes.sphericalEntropy (a n) -
        MetricCodes.sphericalEntropy (b n))
      atTop (𝓝 (-Real.logb 2 c)) := by
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ha
  have hnormalized : Tendsto
      (fun n => ((a n)⁻¹ + b n / a n) / ((a n)⁻¹ + 1))
      atTop (𝓝 c) := by
    convert (hinv.add hratio).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  have hshifted : Tendsto
      (fun n => (1 + b n) / (1 + a n)) atTop (𝓝 c) := by
    apply hnormalized.congr'
    filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hn
    field_simp
  have hlog : Tendsto
      (fun n => Real.logb 2 ((1 + b n) / (1 + a n)))
      atTop (𝓝 (Real.logb 2 c)) :=
    (Real.continuousAt_logb hc.ne').tendsto.comp hshifted
  have hfirst := tendsto_sphericalEntropy_sub_logb_one_add.comp ha
  have hsecond := tendsto_sphericalEntropy_sub_logb_one_add.comp hb
  have hlimit := (hfirst.sub hsecond).sub hlog
  have htarget :
      (1 / Real.log 2 - 1 / Real.log 2) - Real.logb 2 c =
        -Real.logb 2 c := by ring
  rw [htarget] at hlimit
  apply hlimit.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop (0 : ℝ)),
    hb.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hbn
  rw [Real.logb_div (by positivity) (by positivity)]
  simp only [Function.comp_apply]
  ring
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
