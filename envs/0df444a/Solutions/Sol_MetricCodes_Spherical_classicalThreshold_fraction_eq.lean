-- Prove2me | solution 1 for MetricCodes.Spherical.classicalThreshold_fraction_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/b8e7b4f8-0f48-4242-9f7a-4d68f57155b9

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.classicalThreshold s / (1 + MetricCodes.classicalThreshold s) =
      (1 - Real.sqrt (1 - s ^ 2)) /
        (1 + Real.sqrt (1 - s ^ 2)) := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.mpr hrad
  unfold MetricCodes.classicalThreshold
  field_simp [hroot.ne',
    (by positivity : 1 + Real.sqrt (1 - s ^ 2) ≠ 0)]
  apply (div_eq_iff (by nlinarith :
    Real.sqrt (1 - s ^ 2) * 2 + (1 - Real.sqrt (1 - s ^ 2)) ≠ 0)).2
  ring
end MetricCodes.Spherical
