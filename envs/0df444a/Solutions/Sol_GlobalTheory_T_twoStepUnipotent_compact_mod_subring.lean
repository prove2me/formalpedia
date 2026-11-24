-- Prove2me | solution 1 for GlobalTheory.T.twoStepUnipotent_compact_mod_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:04.380633+00:00
-- url     : https://prove2.me/submissions/06a5ebe7-8d12-40b2-94fe-292e7e7b531e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubringStatement
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_compact_mod_subring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S] (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S), Continuous st → (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → (∀ x ∈ S₀, st x ∈ S₀) → e₁ ∈ S₀ → h ∈ S₀ → e₁ * e₁ = e₁ → st e₁ = e₃ → e₁ * e₃ = 0 → e₃ * e₁ = 0 → h + h = 1 → (∀ x, h * x = x * h) → IsCompact K → (∀ x, ∃ y ∈ S₀, x - y ∈ K) → ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) → ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧ γ * g ∈ K' := by
  first | exact @GlobalTheory.TwoStepUnipotent.compact_mod_subring | exact GlobalTheory.TwoStepUnipotent.compact_mod_subring | (intros; apply GlobalTheory.TwoStepUnipotent.compact_mod_subring <;> assumption)
end _root_.GlobalTheory.T
