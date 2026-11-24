-- Prove2me | solution 1 for GlobalTheory.norm_iterate_le_self_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:13.183877+00:00
-- url     : https://prove2.me/submissions/579ee97e-078c-4f7d-8434-256de9747164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_norm_iterate_le_of_contraction

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
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ‖ε^[j] x‖ ≤ ‖x‖ :=
  (norm_iterate_le_of_contraction hc hx j).trans
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num)))
end GlobalTheory
