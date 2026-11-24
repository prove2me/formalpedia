-- Prove2me | solution 1 for GlobalTheory.IterGain.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:10.408802+00:00
-- url     : https://prove2.me/submissions/273be192-2d06-460a-b5b9-91e259d84486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
import Theorems.Thm_GlobalTheory_IterGain_nil_mem
import Theorems.Thm_GlobalTheory_IterGain_append_mem
import Theorems.Thm_GlobalTheory_IterGain_root_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.IterGain
namespace GlobalTheory.IterGain
theorem _root_.solution {G ι : Type} [DecidableEq ι] (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (m : ℕ) (C δ₀ K : ℝ) (Q : G → ℝ) (A : ℕ)
    (hm : m ≠ 0) (hδ₀ : 0 < δ₀) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKm : K ^ m = C)
    (hq : ∀ g, 1 ≤ q g) (hQ1 : ∀ g, 1 ≤ Q g) (hQm : ∀ g, Q g ^ m = q g)
    (hcl : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒)
    (hgain : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i))
    (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ words B k, 0 ≤ c l) →
      (∀ l ∈ words B k, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
      ∀ g, ‖ψ g‖ * Q g ^ k ≤ Ck * q g ^ A * ∑ l ∈ words B k, c l := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro ψ _ c _ hc g
    have h := hc [] (nil_mem B 0) g
    simp only [List.foldr_nil] at h
    simp [words]
    linarith
  | succ k ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := ih
    have hK0 : 0 ≤ K := by linarith
    have hC0 : 0 ≤ C := by linarith
    have hQ0 : ∀ g, 0 ≤ Q g := fun g => by linarith [hQ1 g]
    have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
    set M := K / δ₀ with hM
    have hM0 : 0 ≤ M := div_nonneg hK0 hδ₀.le
    set X1 := M ^ (k + 1)
    set X2 := C * K ^ (k + 1) * Ck * C ^ A * ((B.card : ℝ) * ((words B k).card : ℝ))
    have hX1 : 0 ≤ X1 := pow_nonneg hM0 _
    have hX2 : 0 ≤ X2 := by positivity
    refine ⟨X1 + X2, add_nonneg hX1 hX2, ?_⟩
    intro ψ hψ c hc0 hc g
    set T := ∑ l ∈ words B (k + 1), c l with hT
    have hT0 : 0 ≤ T := sum_nonneg hc0
    have hqA : 0 ≤ q g ^ A := pow_nonneg (hq0 g) _
    obtain ⟨δ, hδ, _, hδq, hcase⟩ := hgain g
    have hδQ : δ * Q g ≤ K := by
      apply root_le hm (mul_nonneg hδ.le (hQ0 g)) hK0
      rw [mul_pow, hQm, hKm]; linarith [mul_comm (q g) (δ ^ m)]
    have hQgw : ∀ w, q g ≤ C * q w → Q g ≤ K * Q w := by
      intro w hw
      apply root_le hm (hQ0 g) (mul_nonneg hK0 (hQ0 w))
      rw [mul_pow, hQm, hKm, hQm]; exact hw
    suffices h : ‖ψ g‖ * Q g ^ (k + 1) ≤ X1 * q g ^ A * T ∨
        ‖ψ g‖ * Q g ^ (k + 1) ≤ X2 * q g ^ A * T by
      have e1 : 0 ≤ X1 * q g ^ A * T := by positivity
      have e2 : 0 ≤ X2 * q g ^ A * T := mul_nonneg (mul_nonneg hX2 hqA) hT0
      rcases h with h | h <;> nlinarith
    rcases hcase with hδ0 | ⟨Ω, hΩ, hbound⟩
    · left
      have hQM : Q g ≤ M := by
        rw [hM, le_div_iff₀ hδ₀]; nlinarith [hQ0 g]
      have h0 : ‖ψ g‖ ≤ c [] * q g ^ A := by simpa using hc [] (nil_mem B _) g
      have hcT : c [] ≤ T := single_le_sum (f := c) (fun l hl => hc0 l hl) (nil_mem B _)
      have hQk : Q g ^ (k + 1) ≤ X1 := pow_le_pow_left₀ (hQ0 g) hQM _
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (c [] * q g ^ A) * X1 :=
            mul_le_mul h0 hQk (pow_nonneg (hQ0 g) _) (by nlinarith [norm_nonneg (ψ g)])
        _ ≤ (T * q g ^ A) * X1 := by gcongr
        _ = X1 * q g ^ A * T := by ring
    · right
      set S : ι → ℝ := fun i => ∑ l ∈ words B k, c (l ++ [i]) with hS
      have hS0 : ∀ i ∈ B, 0 ≤ S i := fun i hi =>
        sum_nonneg (fun l hl => hc0 _ (append_mem hl hi))
      have hQgk : 0 < Q g ^ k := pow_pos (by linarith [hQ1 g]) _
      set P := K ^ k * Ck * C ^ A * q g ^ A with hP
      have hP0 : 0 ≤ P := by positivity
      set ci : ι → ℝ := fun i => P * S i / Q g ^ k with hci
      have hDr : ∀ i ∈ B, 0 ≤ ci i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ ci i := by
        intro i hi
        refine ⟨div_nonneg (mul_nonneg hP0 (hS0 i hi)) hQgk.le, ?_⟩
        intro w hw
        have hb := hCk (Dr i ψ) (hcl ψ hψ i hi) (fun l => c (l ++ [i]))
          (fun l hl => hc0 _ (append_mem hl hi))
          (fun l hl g' => by
            have := hc (l ++ [i]) (append_mem hl hi) g'
            simpa [List.foldr_append] using this) w
        have h1 : Q g ^ k ≤ K ^ k * Q w ^ k := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hQ0 g) (hQgw w (hΩ w hw).2) k
        have h2 : q w ^ A ≤ C ^ A * q g ^ A := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hq0 w) (hΩ w hw).1 A
        rw [hci, le_div_iff₀ hQgk]
        calc ‖Dr i ψ w‖ * Q g ^ k ≤ ‖Dr i ψ w‖ * (K ^ k * Q w ^ k) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = K ^ k * (‖Dr i ψ w‖ * Q w ^ k) := by ring
          _ ≤ K ^ k * (Ck * q w ^ A * S i) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hK0 _)
          _ ≤ K ^ k * (Ck * (C ^ A * q g ^ A) * S i) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0 _)
              apply mul_le_mul_of_nonneg_right _ (hS0 i hi)
              exact mul_le_mul_of_nonneg_left h2 hCk0
          _ = P * S i := by rw [hP]; ring
      have hmain := hbound ψ hψ ci hDr
      have hsum : ∑ i ∈ B, ci i = P * (∑ i ∈ B, S i) / Q g ^ k := by
        rw [hci]; simp only; rw [← Finset.sum_div, ← Finset.mul_sum]
      have hSsum : ∑ i ∈ B, S i ≤ (B.card : ℝ) * ((words B k).card : ℝ) * T := by
        calc ∑ i ∈ B, S i ≤ ∑ i ∈ B, ∑ l ∈ words B k, T :=
              sum_le_sum (fun i hi => sum_le_sum (fun l hl =>
                single_le_sum (f := c) (fun l hl => hc0 l hl) (append_mem hl hi)))
          _ = (B.card : ℝ) * ((words B k).card : ℝ) * T := by
              simp [sum_const, nsmul_eq_mul]; ring
      have hSum0 : 0 ≤ ∑ i ∈ B, S i := sum_nonneg hS0
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (C * δ * ∑ i ∈ B, ci i) * Q g ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hmain (pow_nonneg (hQ0 g) _)
        _ = C * (δ * Q g) * (P * ∑ i ∈ B, S i) := by
            rw [hsum]; field_simp; ring
        _ ≤ C * K * (P * ((B.card : ℝ) * ((words B k).card : ℝ) * T)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hδQ hC0)
              (mul_le_mul_of_nonneg_left hSsum hP0) (mul_nonneg hP0 hSum0) (mul_nonneg hC0 hK0)
        _ = X2 * q g ^ A * T := by rw [hP]; ring
end GlobalTheory.IterGain
