-- Prove2me | solution 1 for GlobalTheory.T.sum_fibre_two_index_encard_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:21.461123+00:00
-- url     : https://prove2.me/submissions/37b54bbc-9fca-4138-bddd-9cfadf8a7626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumFibreTwoIndexEncardBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumFibreTwoIndexEncardBoundStatement
import Theorems.Thm_GlobalTheory_sum_fibre_two_index_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  first | exact @GlobalTheory.sum_fibre_two_index_bound | exact GlobalTheory.sum_fibre_two_index_bound | (intros; apply GlobalTheory.sum_fibre_two_index_bound <;> assumption)
end _root_.GlobalTheory.T
