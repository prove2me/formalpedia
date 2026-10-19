-- Prove2me | solution 1 for MetricCodes.Spherical.classicalThreshold_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/29191e26-28e5-45d4-9064-8e9f71577926

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    ContinuousAt MetricCodes.classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : Real.sqrt (1 - s ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hrad).ne'
  unfold MetricCodes.classicalThreshold
  fun_prop (disch := aesop)
end MetricCodes.Spherical
