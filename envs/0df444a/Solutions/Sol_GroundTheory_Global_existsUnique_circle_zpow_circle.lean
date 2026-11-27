-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_circle_zpow_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:17.664092+00:00
-- url     : https://prove2.me/submissions/4ed7b053-ea77-470f-a610-3077bc057882

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_circle_coe_zpow
import Theorems.Thm_GroundTheory_Global_existsUnique_circle_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (χ : Circle →ₜ* Circle) :
    ∃! m : ℤ, ∀ z : Circle, χ z = z ^ m := by
  refine (existsUnique_congr fun m => forall_congr' fun z => ?_).mpr
    (existsUnique_circle_zpow (circleToUnits.comp χ))
  show χ z = z ^ m ↔ (χ z : ℂ) = (z : ℂ) ^ m
  rw [← circle_coe_zpow, Circle.coe_inj]
end GroundTheory.Global
