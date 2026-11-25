-- Prove2me | solution 1 for GroundTheory.Global.norm_sq_sub_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:53.291469+00:00
-- url     : https://prove2.me/submissions/e039e01a-abb4-4745-8557-bb80e2adfec4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups

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
namespace GroundTheory.Global
theorem _root_.solution {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) :
    3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have h1 : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
  have h2 : (3 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have : z + 1 = 2 - (1 - z) := by ring
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    have h4 : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    calc (3 : ℝ) / 2 ≤ ‖(2 : ℂ)‖ - ‖1 - z‖ := by rw [h3, h4]; linarith
      _ ≤ ‖(2 : ℂ) - (1 - z)‖ := norm_sub_norm_le _ _
      _ = ‖z + 1‖ := by rw [this]
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (z - 1)]
end GroundTheory.Global
