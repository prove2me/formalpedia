-- Prove2me | solution 1 for GlobalTheory.isBigO_doublingLog_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:34.311858+00:00
-- url     : https://prove2.me/submissions/43320e33-395b-4ff3-bc78-1b8a3c2c6eeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_dist_doublingLog_le_of_contraction
import Theorems.Thm_GlobalTheory_exists_ball_contraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    (fun x => doublingLog ε x - x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
  obtain ⟨r, hr, C, hC0, hc, hC⟩ := exists_ball_contraction h
  refine IsBigO.of_bound (64 / 7 * C) ?_
  filter_upwards [ball_mem_nhds 0 hr] with x hx
  have := dist_doublingLog_le_of_contraction hc hC0 hC hx 0
  rw [dist_comm, dist_eq_norm] at this
  simpa using this
end GlobalTheory
