-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.rounded_positive_exponent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:12:22.922375+00:00
-- url     : https://prove2.me/submissions/cea610e7-4c79-40d8-8d5b-76a2ef997a83

import Mathlib
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators


theorem solution (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i) (D : ℝ) (hD : 0 ≤ D) : ∀ i, ∃ N : ℕ, 0 < N ∧ D < (N : ℝ) * w i ∧ (N : ℝ) * w i ≤ D + w i := by
  intro i
  have hwi := hw i
  refine ⟨⌊D / w i⌋₊ + 1, Nat.succ_pos _, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (D / w i)
    rw [div_lt_iff₀ hwi] at this
    push_cast; linarith
  · have h1 : (⌊D / w i⌋₊ : ℝ) ≤ D / w i := Nat.floor_le (div_nonneg hD hwi.le)
    have h2 : (⌊D / w i⌋₊ : ℝ) * w i ≤ D := by rwa [le_div_iff₀ hwi] at h1
    push_cast; linarith

