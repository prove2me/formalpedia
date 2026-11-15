-- Prove2me | solution 1 for Komlos.bansal_jiang_beck_fiala
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T02:55:05.94585+00:00
-- url     : https://prove2.me/submissions/97e0d461-e820-4edf-a478-6ce88993c440
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Komlos_model
import Theorems.Thm_Komlos_bansal_jiang_stronger_beck_fiala

open Komlos

theorem solution :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ (t n m : ℕ) (A : Fin m → Fin n → ℝ),
        (∀ i j, A i j = 0 ∨ A i j = 1) →
        (∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) →
        C₀ * Real.log (n + 2) ^ 2 ≤ (t : ℝ) →
        ∃ ε : Fin n → ℝ, IsSignVector ε ∧
          ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt t := by
  obtain ⟨C, hC, h⟩ := bansal_jiang_stronger_beck_fiala
  refine ⟨2, C, by norm_num, hC, ?_⟩
  intro t n m A h01 hdeg hthr
  -- a `0/1` matrix is a `0/±1` matrix
  have hA : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := fun i j =>
    (h01 i j).elim Or.inl (fun h1 => Or.inr (Or.inl h1))
  -- for a `0/1` matrix the non-zero entries of a column are its ones
  have hdeg' : ∀ j, ({i | A i j ≠ 0} : Finset (Fin m)).card ≤ t := by
    intro j
    have hset : ({i | A i j ≠ 0} : Finset (Fin m)) = ({i | A i j = 1} : Finset (Fin m)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 i j with h0 | h1
      · simp [h0]
      · simp [h1]
    rw [hset]
    exact hdeg j
  obtain ⟨ε, hε, hb⟩ := h t n m A hA hdeg'
  refine ⟨ε, hε, fun i => ?_⟩
  have hbi := hb i
  -- the threshold places `(t, n)` in the third regime of the bound
  have hL : 0 < Real.log ((n : ℝ) + 2) := by
    apply Real.log_pos
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlt : Real.log ((n : ℝ) + 2) ^ 2 < (t : ℝ) := by
    have : 0 < Real.log ((n : ℝ) + 2) ^ 2 := by positivity
    linarith
  have h2 : ¬ ((t : ℝ) ≤ Real.log ((n : ℝ) + 2) ^ 2) := not_le.mpr hlt
  have h1 : ¬ ((t : ℝ) ≤ Real.sqrt (Real.log ((n : ℝ) + 2))) := by
    intro hle
    have htpos : (0 : ℝ) < (t : ℝ) := lt_trans (by positivity) hlt
    have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
      have : 0 < t := by exact_mod_cast htpos
      exact_mod_cast this
    have hs1 : 1 ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) := le_trans ht1 hle
    have hsq : Real.sqrt (Real.log ((n : ℝ) + 2)) * Real.sqrt (Real.log ((n : ℝ) + 2))
        = Real.log ((n : ℝ) + 2) := Real.mul_self_sqrt hL.le
    have hLs : Real.sqrt (Real.log ((n : ℝ) + 2)) ≤ Real.log ((n : ℝ) + 2) := by nlinarith
    have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := le_trans hs1 hLs
    have hLL : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) ^ 2 := by nlinarith
    linarith
  rw [if_neg h1, if_neg h2] at hbi
  exact hbi
