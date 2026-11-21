-- Prove2me | solution 1 for MomentSearch.proposition_10
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:44:59.17818+00:00
-- url     : https://prove2.me/submissions/f08a0717-1825-4c0a-9c0a-b5d4a9a1c0c7

import Mathlib
import Definitions.Def_MomentSearch_moment
import Theorems.Thm_MomentSearch_lemma_11
import Theorems.Thm_MomentSearch_lemma_12
import Theorems.Thm_MomentSearch_lemma_13
import Theorems.Thm_MomentSearch_lemma_14

open MomentSearch

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 3 ≤ n → 1 ≤ k → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
      ∀ m m₀ : Fin n,
        ((n : ℝ) - 1) / 4 ≤ ((m : ℕ) : ℝ) → ((m : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
        ((n : ℝ) - 1) / 4 ≤ ((m₀ : ℕ) : ℝ) → ((m₀ : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
        ∃ p p' : Fin n → ℝ, ∃ γ : ℝ,
          p ∈ stdSimplex ℝ (Fin n) ∧ p' ∈ stdSimplex ℝ (Fin n) ∧
          γ ≤ C * ((k : ℝ) / ((n : ℝ) - 1)) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| ∧
          1 - γ ≤ p m ∧ 1 - γ ≤ p' m₀ ∧
          ∀ i : ℕ, i ≤ k → moment p i = moment p' i := by
  obtain ⟨C₁, hC₁⟩ := MomentSearch.lemma_13
  have hC₁one : (1 : ℝ) ≤ C₁ := by
    have h := hC₁ 2 0 (by decide) (by norm_num) (1 : Polynomial ℝ) (by simp)
      (by intro t; simp) 0 ⟨by norm_num, by norm_num⟩
    simpa using h
  have hC₁pos : 0 < C₁ := zero_lt_one.trans_le hC₁one
  refine ⟨4 * C₁ / Real.sqrt 5, by positivity, ?_⟩
  intro n k hn hk1 hk m m₀ hmlo hmhi hm₀lo hm₀hi
  have hn₂ : 2 ≤ n := le_trans (by decide) hn
  obtain ⟨a, ha, hnorm⟩ := (MomentSearch.lemma_12 hn₂ k m m₀).2
  obtain ⟨p, p', hp, hp', hmom, hpeak, hpeak'⟩ := MomentSearch.lemma_11 hn₂ k m m₀ a ha
  refine ⟨p, p', (1 / 2) * ∑ t : Fin n, |a t|, hp, hp', ?_, hpeak, hpeak', hmom⟩
  rw [hnorm]
  have hcorrection := MomentSearch.lemma_14 C₁ hC₁ n k hk1 hk m m₀
    ⟨hmlo, hmhi⟩ ⟨hm₀lo, hm₀hi⟩
  calc
    (1 / 2) * correctionNorm n k m m₀ ≤
        (1 / 2) * (8 * C₁ / Real.sqrt 5 *
          ((k : ℝ) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| / ((n : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left hcorrection (by norm_num)
    _ = 4 * C₁ / Real.sqrt 5 * ((k : ℝ) / ((n : ℝ) - 1)) *
        |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| := by ring
