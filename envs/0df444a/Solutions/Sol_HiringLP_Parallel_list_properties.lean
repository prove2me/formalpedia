-- Prove2me | solution 1 for HiringLP.Parallel.list_properties
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:18:20.858472+00:00
-- url     : https://prove2.me/submissions/db13f3ef-b850-4732-881c-abacf75baa1a

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

open HiringLP.Parallel Finset

theorem solution {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ)
    (hy : LPFeasible I y) (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ)
    (Y : Finset (Fin n × Fin k)) (hY : μ Y ≠ 0) :
    (∀ j, degRight Y j ≤ I.T) ∧ ∀ i, degLeft Y i ≤ 1 := by
  constructor
  · intro j
    have hc : ⌈∑ i, y i j⌉ ≤ (I.T : ℤ) := by
      rw [Int.ceil_le]; exact_mod_cast hy.1 j
    have hf : ⌊∑ i, y i j⌋ ≤ ⌈∑ i, y i j⌉ := Int.floor_le_ceil _
    have := hμ.degree_right Y hY j
    have h2 : (degRight Y j : ℤ) ≤ (I.T : ℤ) := by
      rcases this with h | h <;> rw [h] <;> omega
    exact_mod_cast h2
  · intro i
    have hc : ⌈∑ j, y i j⌉ ≤ (1 : ℤ) := by
      rw [Int.ceil_le]; exact_mod_cast hy.2.2.1 i
    have hf : ⌊∑ j, y i j⌋ ≤ ⌈∑ j, y i j⌉ := Int.floor_le_ceil _
    have := hμ.degree_left Y hY i
    have h2 : (degLeft Y i : ℤ) ≤ 1 := by
      rcases this with h | h <;> rw [h] <;> omega
    exact_mod_cast h2
