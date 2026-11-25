-- Prove2me | solution 1 for GlobalTheory.tendsto_doublingLog_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:55.96442+00:00
-- url     : https://prove2.me/submissions/87e36ace-4ce9-4ff4-a26f-a7f7e434aea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_dist_two_pow_smul_iterate_succ_le

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
theorem _root_.solution (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2)
    {x : V} (hx : x ∈ ball (0 : V) r) :
    Tendsto (fun j : ℕ => (2 : ℂ) ^ j • ε^[j] x) atTop (𝓝 (doublingLog ε x)) :=
  (cauchySeq_of_le_geometric (25 / 32) (2 * C * ‖x‖ ^ 2) (by norm_num)
    (dist_two_pow_smul_iterate_succ_le hc hC0 hC hx)).tendsto_limUnder
end GlobalTheory
