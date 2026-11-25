-- Prove2me | solution 1 for GroundTheory.Global.Complex.units_noSmallSubgroups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:00:38.844845+00:00
-- url     : https://prove2.me/submissions/57897d7b-b13e-42d1-84b2-1ed2bdf8df71

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_Complex_units_subgroup_eq_bot_of_norm_sub_one_lt

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
open GroundTheory.Global.Complex
namespace GroundTheory.Global.Complex
theorem _root_.solution : NoSmallSubgroups ℂˣ := by
  refine ⟨{z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    units_subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : ℂˣ ↦ ‖(z : ℂ) - 1‖ :=
    (Units.continuous_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
end GroundTheory.Global.Complex
