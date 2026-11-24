-- Prove2me | solution 1 for GlobalTheory.iterate_mem_ball_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:47.603963+00:00
-- url     : https://prove2.me/submissions/6c8f5386-57f1-4dca-b01d-3876db6a436a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_norm_iterate_le_self_of_contraction

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
omit [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ε^[j] x ∈ ball (0 : V) r :=
  mem_ball_zero_iff.mpr
    ((norm_iterate_le_self_of_contraction hc hx j).trans_lt (mem_ball_zero_iff.mp hx))
end GlobalTheory
