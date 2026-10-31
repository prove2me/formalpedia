-- Prove2me | solution 1 for MarketFreeze.Hetero.eq_A1_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:02:56.924085+00:00
-- url     : https://prove2.me/submissions/aabe60f3-39be-4056-be0c-9a3dd9750aab

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model
open MarketFreeze.Hetero

theorem solution(P : Params) (h0 : Standing P) (h1 : Assumption1 P) :
    CondA1 P ↔ 0 < dPi P 0 ∧ dPi P P.θbar < 0 := by
  obtain ⟨hI, hδ0, hδ1, ht0, htI, hc, hψ⟩ := h0
  obtain ⟨hX1, hX2⟩ := h1
  have hX : 0 < P.X := by nlinarith
  have ht1 : P.θbar < 1 := by
    have : P.I / P.X < 1 := (div_lt_one hX).2 (by nlinarith)
    linarith
  have h1t : 0 < 1 - P.θbar := by linarith
  have hK : 0 < 1 + 2 * P.ψ / (1 - P.θbar) := by positivity
  have hK0 : 0 < 1 + 2 * P.ψ := by linarith
  have n1 : 1 - P.θbar ≠ 0 := h1t.ne'
  have n2 : 1 - P.θbar + 2 * P.ψ ≠ 0 := by linarith
  have n3 : 1 + 2 * P.ψ ≠ 0 := hK0.ne'
  have e0 : dPi P 0 = (1 + 2 * P.ψ) *
      ((1 / 2 : ℝ) * P.X / (1 + 2 * P.ψ) + (1 / 2 : ℝ) * P.Y 0 - P.c) := by
    unfold dPi piS piNS Ehom; field_simp; ring
  have e1 : dPi P P.θbar = (1 + 2 * P.ψ / (1 - P.θbar)) *
      ((1 / 2 : ℝ) * (1 - P.θbar) * P.X / (1 + 2 * P.ψ / (1 - P.θbar)) -
        P.θbar * (P.X - P.I) + (1 / 2 : ℝ) * (1 - P.θbar) * P.Y P.θbar - P.c) := by
    unfold dPi piS piNS Ehom; field_simp; ring
  unfold CondA1
  rw [e0, e1]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨mul_pos hK0 (by linarith), mul_neg_of_pos_of_neg hK (by linarith)⟩
  · rintro ⟨a, b⟩
    refine ⟨?_, ?_⟩
    · by_contra hc'
      push_neg at hc'
      nlinarith [mul_nonneg hK.le (sub_nonneg.2 hc')]
    · by_contra hc'
      push_neg at hc'
      nlinarith [mul_nonneg hK0.le (sub_nonneg.2 hc')]
