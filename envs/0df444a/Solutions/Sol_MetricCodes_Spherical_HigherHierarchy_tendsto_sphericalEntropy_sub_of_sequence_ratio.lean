-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_sphericalEntropy_sub_of_sequence_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/d680a9ae-c275-448f-9c7d-b220578ba799

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_sphericalEntropy_sub_logb_one_add
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_shifted_degree_ratio_of_tendsto_ratio

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
theorem _root_.solution
    {u v : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hu : Tendsto u atTop atTop)
    (hv : Tendsto v atTop atTop)
    (hratio : Tendsto (fun n => v n / u n) atTop (nhds d)) :
    Tendsto (fun n =>
      MetricCodes.sphericalEntropy (u n) -
        MetricCodes.sphericalEntropy (v n))
      atTop (nhds (-Real.logb 2 d)) := by
  have hshifted :=
    tendsto_shifted_degree_ratio_of_tendsto_ratio hu hratio
  have hlog : Tendsto
      (fun n => Real.logb 2 ((1 + v n) / (1 + u n)))
        atTop (nhds (Real.logb 2 d)) :=
    (Real.continuousAt_logb hd.ne').tendsto.comp hshifted
  have hfirst :=
    CompactificationEntropy.tendsto_sphericalEntropy_sub_logb_one_add.comp hu
  have hsecond :=
    CompactificationEntropy.tendsto_sphericalEntropy_sub_logb_one_add.comp hv
  have hlimit := (hfirst.sub hsecond).sub hlog
  have htarget :
      (1 / Real.log 2 - 1 / Real.log 2) - Real.logb 2 d =
        -Real.logb 2 d := by ring
  rw [htarget] at hlimit
  apply hlimit.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ)),
    hv.eventually (eventually_gt_atTop (0 : ℝ))] with n hun hvn
  rw [Real.logb_div (by positivity) (by positivity)]
  simp only [Function.comp_apply]
  ring
end MetricCodes.Spherical.HigherHierarchy
