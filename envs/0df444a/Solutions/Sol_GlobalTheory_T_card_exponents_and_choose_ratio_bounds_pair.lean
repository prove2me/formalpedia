-- Prove2me | solution 1 for GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:10.089223+00:00
-- url     : https://prove2.me/submissions/e9f86c07-232f-4898-9f25-aee2e4201489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPair
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPairStatement
import Theorems.Thm_GlobalTheory_card_exponents_and_choose_ratio_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  first | exact @GlobalTheory.card_exponents_and_choose_ratio_bounds | exact GlobalTheory.card_exponents_and_choose_ratio_bounds | (intros; apply GlobalTheory.card_exponents_and_choose_ratio_bounds <;> assumption)
end _root_.GlobalTheory.T
