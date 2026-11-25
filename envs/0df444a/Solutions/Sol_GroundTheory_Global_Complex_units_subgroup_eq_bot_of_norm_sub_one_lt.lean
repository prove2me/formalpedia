-- Prove2me | solution 1 for GroundTheory.Global.Complex.units_subgroup_eq_bot_of_norm_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:25.559576+00:00
-- url     : https://prove2.me/submissions/1a8a29b7-8138-402e-8c8c-4166ed6cb860

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_eq_one_of_sq_mem

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
theorem _root_.solution (H : Subgroup ℂˣ)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Units.val_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set ℂˣ)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw
end GroundTheory.Global.Complex
