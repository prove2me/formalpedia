-- Prove2me | solution 1 for MetricCodes.Spherical.classicalEndpointUpper_continuousAt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/04499108-d42d-4c13-991c-325f57e69434

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
theorem _root_.solution :
    ContinuousAt classicalEndpointUpper 1 := by
  unfold classicalEndpointUpper
  have harg :
      (2 * Real.sqrt (2 * (1 + (1 : ℝ))) /
        (1 + Real.sqrt (1 - (1 : ℝ) ^ 2))) ≠ 0 := by norm_num
  have hden : 1 + Real.sqrt (1 - (1 : ℝ) ^ 2) ≠ 0 := by norm_num
  have hu : ContinuousAt
      (fun s : ℝ => Real.sqrt (1 - s ^ 2)) 1 := by fun_prop
  have hv : ContinuousAt
      (fun s : ℝ => Real.sqrt (2 * (1 + s))) 1 := by fun_prop
  have hquot : ContinuousAt
      (fun s : ℝ => 2 * Real.sqrt (2 * (1 + s)) /
        (1 + Real.sqrt (1 - s ^ 2))) 1 :=
    (continuousAt_const.mul hv).div (continuousAt_const.add hu) hden
  have hfraction : ContinuousAt
      (fun s : ℝ => (1 - Real.sqrt (1 - s ^ 2)) /
        (1 + Real.sqrt (1 - s ^ 2))) 1 :=
    (continuousAt_const.sub hu).div (continuousAt_const.add hu) hden
  unfold Real.logb
  exact (hquot.log harg).div_const (Real.log 2) |>.sub
    (hfraction.div_const (Real.log 2))
end MetricCodes.Spherical
