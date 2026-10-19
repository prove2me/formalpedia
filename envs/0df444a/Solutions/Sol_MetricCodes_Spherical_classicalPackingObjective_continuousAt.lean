-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingObjective_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/25f7bd2c-2c68-4012-87a2-8a9a434bbf04

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_continuousAt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : -1 < s) (hs' : s < 1) :
    ContinuousAt classicalPackingObjective s := by
  have hden : (1 : ℝ) - s ≠ 0 := by linarith
  have harg : (2 : ℝ) / (1 - s) ≠ 0 := by positivity
  have hratio : ContinuousAt (fun t : ℝ => 2 / (1 - t)) s :=
    continuousAt_const.div
      (continuousAt_const.sub continuousAt_id) hden
  have hlog : ContinuousAt
      (fun t : ℝ => Real.logb 2 (2 / (1 - t))) s := by
    fun_prop (disch := aesop)
  unfold classicalPackingObjective
  exact ((continuousAt_const.mul hlog).sub
    (sphericalEntropy_continuous.continuousAt.comp
      (classicalThreshold_continuousAt hs hs')))
end MetricCodes.Spherical
