-- Prove2me | solution 1 for GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:12.919059+00:00
-- url     : https://prove2.me/submissions/0e6545b6-d94b-4876-8504-7db4210c332b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeOfGrowthInRadius
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeOfGrowthInRadiusStatement
import Theorems.Thm_GlobalTheory_rank_le_of_growth_in_radius


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
theorem _root_.solution : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ → (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) → (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) → ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  first | exact @GlobalTheory.rank_le_of_growth_in_radius | exact GlobalTheory.rank_le_of_growth_in_radius | (intros; apply GlobalTheory.rank_le_of_growth_in_radius <;> assumption)
end _root_.GlobalTheory.T
