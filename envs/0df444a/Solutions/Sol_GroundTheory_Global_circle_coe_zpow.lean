-- Prove2me | solution 1 for GroundTheory.Global.circle_coe_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:06.720726+00:00
-- url     : https://prove2.me/submissions/1347d0e9-3e3d-47b3-bcb2-5bdf8a85d3e4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_circleToUnits



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (z : Circle) (m : ℤ) : ((z ^ m : Circle) : ℂ) = (z : ℂ) ^ m := by
  rw [← coe_circleToUnits, map_zpow, Units.val_zpow_eq_zpow_val, coe_circleToUnits]
end GroundTheory.Global
