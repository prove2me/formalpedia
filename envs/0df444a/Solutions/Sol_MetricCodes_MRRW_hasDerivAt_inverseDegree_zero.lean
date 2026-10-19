-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_inverseDegree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/9eac8ee0-791e-4eb5-977c-119ec05339cf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution :
    HasDerivAt inverseDegree 0 0 := by
  have hradical :
      HasDerivAt (fun r : ℝ => 1 - r ^ 2) 0 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub (1 : ℝ)
  have hroot :
      HasDerivAt (fun r : ℝ => Real.sqrt (1 - r ^ 2)) 0 0 := by
    simpa using
      hradical.sqrt (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  unfold inverseDegree
  simpa [Function.comp_def] using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
      hroot).div_const (2 : ℝ)
end MetricCodes.MRRW
