-- Prove2me | solution 1 for GlobalTheory.card_exponents_and_choose_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:45.570668+00:00
-- url     : https://prove2.me/submissions/fa177295-6204-4966-99e8-645cb010999e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
import Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPair
import Theorems.Thm_GlobalTheory_card_exponents_sum_lt_sub
import Theorems.Thm_GlobalTheory_le_of_add_mul_choose_pred_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  intro D T
  refine ⟨fun _ h => card_exponents_sum_lt_sub D T h, fun δ d ρ hD hT hd =>
    ⟨le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd, fun h => ?_⟩⟩
  refine le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd (le_trans ?_ h)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.choose_le_choose D (by omega))) _
end GlobalTheory
