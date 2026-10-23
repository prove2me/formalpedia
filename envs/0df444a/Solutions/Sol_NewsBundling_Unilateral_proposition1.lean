-- Prove2me | solution 1 for NewsBundling.Unilateral.proposition1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:05:18.080284+00:00
-- url     : https://prove2.me/submissions/1f43a7f1-d30c-42bf-bbc3-206f173b2a63

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting
import Theorems.Thm_NewsBundling_Unilateral_lemma1_benchmark
import Theorems.Thm_NewsBundling_Unilateral_lemma4_equilibrium_quality
import Theorems.Thm_NewsBundling_Unilateral_prop1_qL_lt_qhat_lt_qH
import Theorems.Thm_NewsBundling_Unilateral_consumer_surplus_eq
import Theorems.Thm_NewsBundling_Unilateral_eq2_publisher_profit

set_option autoImplicit false
open NewsBundling.Unilateral

theorem solution (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, IsSPE β φ0 φ1 c Λ σ) ∧
    (∃ σb, IsSPE β φ0 φ1 c 0 σb) ∧
    (∀ σ σb, IsSPE β φ0 φ1 c Λ σ →
      IsSPE β φ0 φ1 c 0 σb →
        eqProfit β φ1 c σ < eqProfit β φ1 c σb ∧
        (c ≠ cdagger β φ1 Λ →
          (σb.quality < σ.quality ↔ c < cdagger β φ1 Λ) ∧
          (consumerSurplus σb < consumerSurplus σ ↔ c < cdagger β φ1 Λ))) ∧
    (c = cdagger β φ1 Λ →
      ∀ σb, IsSPE β φ0 φ1 c 0 σb →
        ∃ σ, IsSPE β φ0 φ1 c Λ σ ∧ σ.quality < σb.quality) := by
  have hS := h
  obtain ⟨⟨hφ0, hφ0'⟩, ⟨hφ1, hφ1'⟩, hφβ, hβc, hΛ0, hΛ1⟩ := h
  have hβ : 0 < β := by linarith
  have hc0 : 0 < c := by linarith
  have hΛ1' : Λ < 1 := by linarith
  obtain ⟨exB, uniqB⟩ := lemma1_benchmark β φ0 φ1 c hβ hβc
  obtain ⟨ex, qual, crossover⟩ := lemma4_equilibrium_quality β φ0 φ1 c Λ hS
  obtain ⟨hLq, hqH⟩ := prop1_qL_lt_qhat_lt_qH β φ1 c Λ hc0 hφβ hΛ0 hΛ1'
  have cs := consumer_surplus_eq β φ0 φ1 c ⟨hφ0, hφ0'⟩
  refine ⟨ex, exB, fun σ σb hσ hσb => ?_, fun heq σb hσb => ?_⟩
  · obtain ⟨hqb, hpb⟩ := uniqB σb hσb
    have hq := hσ.2.2.1
    have csσ := cs Λ hΛ0.le hΛ1' σ hσ
    have csb := cs 0 le_rfl one_pos σb hσb
    refine ⟨?_, fun hne => ?_⟩
    · rw [hpb]
      unfold eqProfit
      rw [eq2_publisher_profit β φ0 φ1 c Λ hS σ hσ _ hq]
      have e2 : β ^ 2 / (2 * c) - (β * σ.quality - c * σ.quality ^ 2 / 2) =
          (c * σ.quality - β) ^ 2 / (2 * c) := by field_simp; ring
      split_ifs with hle
      · rcases eq_or_lt_of_le hq.1 with h0 | h0
        · rw [← h0]
          have : 0 < β ^ 2 / (2 * c) := by positivity
          linarith
        · have : 0 ≤ (c * σ.quality - β) ^ 2 / (2 * c) := by positivity
          have : 0 < (β - φ1) * σ.quality := mul_pos (by linarith) h0
          linarith
      · push_neg at hle
        have hk : 0 < 1 - Λ := by linarith
        have e : φ1 * Λ * (1 - σ.quality) / (1 - Λ) + β * (σ.quality - Λ) / (1 - Λ) -
            c * σ.quality ^ 2 / 2 = β * σ.quality - c * σ.quality ^ 2 / 2 -
              (β - φ1) * Λ * (1 - σ.quality) / (1 - Λ) := by
          field_simp; ring
        rw [e]
        rcases eq_or_lt_of_le hq.2 with h1 | h1
        · have : 0 < (c * σ.quality - β) ^ 2 / (2 * c) := by
            rw [h1]; apply div_pos _ (by positivity); nlinarith
          have : (β - φ1) * Λ * (1 - σ.quality) / (1 - Λ) = 0 := by rw [h1]; simp
          linarith
        · have : 0 < (β - φ1) * Λ * (1 - σ.quality) / (1 - Λ) := by
            apply div_pos _ hk
            exact mul_pos (mul_pos (by linarith) hΛ0) (by linarith)
          have : 0 ≤ (c * σ.quality - β) ^ 2 / (2 * c) := by positivity
          linarith
    · have key : σb.quality < σ.quality ↔ c < cdagger β φ1 Λ := by
        rw [hqb]
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rw [(qual σ hσ).2.1 hlt]; exact ⟨fun _ => hlt, fun _ => hqH⟩
        · rw [(qual σ hσ).1 hgt]
          exact ⟨fun h => absurd h (not_lt.2 hLq.le), fun h => absurd h (not_lt.2 hgt.le)⟩
      refine ⟨key, ?_⟩
      rw [← key, csσ, csb]
      have hb0 := hσb.2.2.1.1
      have hq0 := hq.1
      constructor
      · intro h
        by_contra h'
        push_neg at h'
        nlinarith
      · intro h; nlinarith
  · obtain ⟨hqb, _⟩ := uniqB σb hσb
    obtain ⟨⟨σ, hσ, hqσ⟩, _⟩ := crossover heq
    exact ⟨σ, hσ, by rw [hqσ, hqb]; exact hLq⟩
