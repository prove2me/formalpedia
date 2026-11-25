-- Prove2me | solution 1 for GlobalTheory.T.tendsto_div_pow_of_choose_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:49.23381+00:00
-- url     : https://prove2.me/submissions/c49c9952-68da-4314-b50b-d8a10a63ff1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBoundsStatement
import Theorems.Thm_GlobalTheory_tendsto_rank_div_pow_of_choose_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D e δ : ℕ) (r : ℕ → ℕ), 0 < e → (∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ, δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  first | exact @GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | exact GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | (intros; apply GlobalTheory.tendsto_rank_div_pow_of_choose_bounds <;> assumption)
end _root_.GlobalTheory.T
