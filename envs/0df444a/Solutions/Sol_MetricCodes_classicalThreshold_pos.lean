-- Prove2me | solution 1 for MetricCodes.classicalThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/76325ec5-8040-46e7-a196-41084a8faf8b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators InnerProductSpace
namespace MetricCodes
theorem _root_.solution {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    0 < classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 hrad
  have hsqrt' : Real.sqrt (1 - s ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith
  have hrecip : 1 < 1 / Real.sqrt (1 - s ^ 2) := by
    apply (lt_div_iff₀ hsqrt).2
    simpa using hsqrt'
  unfold classicalThreshold
  linarith
end MetricCodes
