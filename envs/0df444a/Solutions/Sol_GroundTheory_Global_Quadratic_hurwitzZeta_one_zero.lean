-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.hurwitzZeta_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:02.03998+00:00
-- url     : https://prove2.me/submissions/499ba245-7a8f-4564-9311-6e7b4d845d4d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution : hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
  rw [show ((1 : ℝ) : UnitAddCircle) = 0 from AddCircle.coe_period 1, hurwitzZeta_zero,
    riemannZeta_zero]
end GroundTheory.Global.Quadratic
