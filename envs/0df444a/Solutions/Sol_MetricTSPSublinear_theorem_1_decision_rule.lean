-- Prove2me | solution 1 for MetricTSPSublinear.theorem_1_decision_rule
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T03:38:25.11092+00:00
-- url     : https://prove2.me/submissions/e759b6d1-a4eb-46ef-8b02-715d0885e434

import Mathlib

theorem solution (M K TSP Mhat L ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hM : 0 ≤ M)
    (hlow : max M (2 * K) ≤ TSP) (hup : TSP ≤ M + K) (hMhat : M ≤ Mhat ∧ Mhat ≤ (1 + ε / 4) * M)
    (hL : 0 ≤ L ∧ L ≤ K) (hL2 : M - K ≤ ε * M → (1 + ε) / 2 * Mhat ≤ L) :
    let out := if (1 + ε) * Mhat / 2 ≤ L then 2 * Mhat else (2 - ε) * Mhat
    TSP ≤ out ∧ out ≤ (2 - ε / 2) * TSP := by
  have hM_le_TSP : M ≤ TSP := (le_max_left M (2 * K)).trans hlow
  have h2K_le_TSP : 2 * K ≤ TSP := (le_max_right M (2 * K)).trans hlow
  have hK_le_M : K ≤ M := by linarith
  have hMhat_nonneg : 0 ≤ Mhat := hM.trans hMhat.1
  have h2_sub : 0 ≤ 2 - ε := by linarith [hε.2]
  have h2_sub_half : 0 ≤ 2 - ε / 2 := by linarith [hε.2]
  dsimp only
  by_cases h : (1 + ε) * Mhat / 2 ≤ L
  · rw [if_pos h]
    constructor
    · -- TSP ≤ 2 * Mhat
      nlinarith [hup, hK_le_M, hMhat.1, hM]
    · -- 2 * Mhat ≤ (2 - ε/2) * TSP
      have hthreshold : (1 + ε) * Mhat ≤ TSP := by
        have h1 : (1 + ε) * Mhat / 2 ≤ K := h.trans hL.2
        linarith
      have hcoef : 2 ≤ (2 - ε / 2) * (1 + ε) := by nlinarith [hε.1, hε.2]
      calc 2 * Mhat ≤ ((2 - ε / 2) * (1 + ε)) * Mhat :=
              mul_le_mul_of_nonneg_right hcoef hMhat_nonneg
        _ = (2 - ε / 2) * ((1 + ε) * Mhat) := by ring
        _ ≤ (2 - ε / 2) * TSP := mul_le_mul_of_nonneg_left hthreshold h2_sub_half
  · rw [if_neg h]
    have hD : ε * M < M - K := by
      by_contra hle
      push_neg at hle
      have hcontra : (1 + ε) * Mhat / 2 ≤ L := by
        have := hL2 hle
        rwa [show (1 + ε) / 2 * Mhat = (1 + ε) * Mhat / 2 by ring] at this
      exact h hcontra
    constructor
    · -- TSP ≤ (2 - ε) * Mhat
      have h1 : TSP ≤ (2 - ε) * M := by nlinarith [hup, hD]
      calc TSP ≤ (2 - ε) * M := h1
        _ ≤ (2 - ε) * Mhat := mul_le_mul_of_nonneg_left hMhat.1 h2_sub
    · -- (2 - ε) * Mhat ≤ (2 - ε/2) * TSP
      have h1 : (2 - ε) * Mhat ≤ (2 - ε) * ((1 + ε / 4) * M) :=
        mul_le_mul_of_nonneg_left hMhat.2 h2_sub
      have h2 : (2 - ε) * ((1 + ε / 4) * M) ≤ (2 - ε / 2) * M := by
        nlinarith [hM, hε.1, hε.2]
      have h3 : (2 - ε / 2) * M ≤ (2 - ε / 2) * TSP :=
        mul_le_mul_of_nonneg_left hM_le_TSP h2_sub_half
      linarith
