-- Prove2me | solution 1 for KellyStochasticNetworks.reversed_process_rates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:59:47.399561+00:00
-- url     : https://prove2.me/submissions/f9714658-e717-4098-b8db-42c32baa7533

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

open KellyStochasticNetworks

theorem solution {S : Type*} [Fintype S] (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) (h : FullBalance π q) :
    (∀ j : S, (∑' k : S, reversedRates π q j k) = ∑' k : S, q j k) ∧
      FullBalance π (reversedRates π q) := by
  -- Total outflow rate of the reversed process equals that of the original.
  have hout : ∀ j : S, (∑' k : S, reversedRates π q j k) = ∑' k : S, q j k := by
    intro j
    have hj := h j
    simp only [tsum_fintype] at hj ⊢
    simp only [reversedRates]
    rw [← Finset.sum_div, ← hj]
    field_simp [(hπ j).ne']
  refine ⟨hout, ?_⟩
  intro j
  rw [hout j]
  have hin : ∀ k : S, π k * reversedRates π q k j = π j * q j k := by
    intro k
    simp only [reversedRates]
    field_simp [(hπ k).ne']
  simp only [hin, tsum_mul_left]
