-- Prove2me | solution 1 for GlobalTheory.dist_doublingLog_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:34.954021+00:00
-- url     : https://prove2.me/submissions/f2cc7c82-54bb-4fa7-8189-d83d9ed78923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_dist_two_pow_smul_iterate_succ_le
import Theorems.Thm_GlobalTheory_tendsto_doublingLog_of_contraction

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
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) :
    dist ((2 : ℂ) ^ j • ε^[j] x) (doublingLog ε x) ≤ 64 / 7 * C * ‖x‖ ^ 2 * (25 / 32) ^ j := by
  refine (dist_le_of_le_geometric_of_tendsto (25 / 32) (2 * C * ‖x‖ ^ 2) (by norm_num)
    (dist_two_pow_smul_iterate_succ_le hc hC0 hC hx)
    (tendsto_doublingLog_of_contraction hc hC0 hC hx) j).trans_eq ?_
  ring
end GlobalTheory
