-- Prove2me | solution 1 for GlobalTheory.T.exists_rapid_decay_of_iterated_gain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:20:37.055292+00:00
-- url     : https://prove2.me/submissions/8b733637-c974-4a9b-a100-51e6de8a62c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecayStatement
import Theorems.Thm_GlobalTheory_iterated_gain_rapid_decay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ)) (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) → (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) → (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G, (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ, (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) → ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) → ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  first | exact @GlobalTheory.iterated_gain_rapid_decay | exact GlobalTheory.iterated_gain_rapid_decay | (intros; apply GlobalTheory.iterated_gain_rapid_decay <;> assumption)
end _root_.GlobalTheory.T
