-- Prove2me | solution 1 for GlobalTheory.T.sum_translates_eq_doubleCoset_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:50.53353+00:00
-- url     : https://prove2.me/submissions/2cfb2d53-7f93-445f-a4a2-f19961ef5883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverageStatement
import Theorems.Thm_GlobalTheory_CosetAvg_sum_translates_eq_avg


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
theorem _root_.solution : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by
  first | exact @GlobalTheory.CosetAvg.sum_translates_eq_avg | exact GlobalTheory.CosetAvg.sum_translates_eq_avg | (intros; apply GlobalTheory.CosetAvg.sum_translates_eq_avg <;> assumption)
end _root_.GlobalTheory.T
