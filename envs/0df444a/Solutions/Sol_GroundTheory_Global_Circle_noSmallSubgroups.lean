-- Prove2me | solution 1 for GroundTheory.Global.Circle.noSmallSubgroups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:00:54.703813+00:00
-- url     : https://prove2.me/submissions/0e53993b-3e76-49c7-b788-aae737fedf9b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_Circle_subgroup_eq_bot_of_norm_sub_one_lt

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
open Topology Filter
open GroundTheory.Global.Circle
namespace GroundTheory.Global.Circle
theorem _root_.solution : NoSmallSubgroups Circle := by
  refine ⟨{z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
end GroundTheory.Global.Circle
