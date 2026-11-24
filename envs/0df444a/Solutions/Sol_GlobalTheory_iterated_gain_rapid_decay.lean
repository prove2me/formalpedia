-- Prove2me | solution 1 for GlobalTheory.iterated_gain_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:16.852278+00:00
-- url     : https://prove2.me/submissions/d0deabef-b3ab-4e5f-bcd5-154b0b62ed21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
import Theorems.Thm_GlobalTheory_IterGain_mem_letters
import Theorems.Thm_GlobalTheory_IterGain_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
open GlobalTheory.IterGain
namespace GlobalTheory
theorem _root_.solution : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) →
    (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) →
    (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) →
    ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧
      ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
        ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  intro G ι B q 𝓒 Dr b C δ₀ hδ₀ hq hcl hgain A N
  classical
  set m := b + 1 with hmdef
  have hm : m ≠ 0 := Nat.succ_ne_zero b
  set C1 := max C 1 with hC1
  have hC1 : 1 ≤ C1 := le_max_right _ _
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
  have hgain' : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C1 ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C1 * q g ∧ q g ≤ C1 * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C1 * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ, hδ1, hqδ, hcase⟩ := hgain g
    refine ⟨δ, hδ, hδ1, ?_, ?_⟩
    · have h1 : q g * δ ^ m ≤ q g * δ ^ b := by
        rw [hmdef, pow_succ, ← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg (hq0 g) (pow_nonneg hδ.le _)) hδ1
      linarith
    · rcases hcase with h | ⟨Ω, hΩ, hbd⟩
      · exact Or.inl h
      · refine Or.inr ⟨Ω, fun w hw => ⟨?_, ?_⟩, ?_⟩
        · exact (hΩ w hw).1.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 g))
        · exact (hΩ w hw).2.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 w))
        · intro ψ hψ c hc
          have hs : 0 ≤ ∑ i ∈ B, c i := sum_nonneg (fun i hi => (hc i hi).1)
          exact (hbd ψ hψ c hc).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC1 hδ.le) hs)
  set K : ℝ := C1 ^ ((m : ℝ)⁻¹) with hK
  set Q : G → ℝ := fun g => q g ^ ((m : ℝ)⁻¹) with hQ
  have hKm : K ^ m = C1 := Real.rpow_inv_natCast_pow (by linarith) hm
  have hK1 : 1 ≤ K := Real.one_le_rpow hC1 (by positivity)
  have hQm : ∀ g, Q g ^ m = q g := fun g => Real.rpow_inv_natCast_pow (hq0 g) hm
  have hQ1 : ∀ g, 1 ≤ Q g := fun g => Real.one_le_rpow (hq g) (by positivity)
  obtain ⟨Ck, _, hCk⟩ := step B q 𝓒 Dr m C1 δ₀ K Q A hm hδ₀ hC1 hK1 hKm hq hQ1 hQm hcl hgain'
    (m * (A + N))
  refine ⟨words B (m * (A + N)), Ck, mem_letters B _, ?_⟩
  intro ψ hψ c hc g
  have hqA : 0 < q g ^ A := pow_pos (by linarith [hq g]) _
  have hc0 : ∀ l ∈ words B (m * (A + N)), 0 ≤ c l := by
    intro l hl
    by_contra h
    push_neg at h
    have h1 := hc l hl g
    have h2 : c l * q g ^ A < 0 := mul_neg_of_neg_of_pos h hqA
    linarith [norm_nonneg (List.foldr Dr ψ l g)]
  have h := hCk ψ hψ c hc0 hc g
  rw [pow_mul, hQm, pow_add] at h
  have h' : q g ^ A * (‖ψ g‖ * q g ^ N) ≤ q g ^ A * (Ck * ∑ l ∈ words B (m * (A + N)), c l) := by
    linarith
  exact le_of_mul_le_mul_left h' hqA
end GlobalTheory
