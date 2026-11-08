-- Prove2me | solution 1 for MultiwaySoS.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:57:21.542829+00:00
-- url     : https://prove2.me/submissions/d2c4efbf-ed04-4eec-829c-3df87f320878

import Mathlib

theorem solution (a : ℕ → ℝ) (h0 : 0 ≤ a 0)
    (ha : ∀ t, a (t + 1) = a t + Real.sqrt (8 * a t) + 2) (t : ℕ) :
    Real.sqrt (8 * a t) - Real.sqrt (8 * a 0) ≤ 4 * t + 2 * Real.log (1 + 2 * t) := by
  have hnn : ∀ t, 0 ≤ a t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [ha]
      linarith [Real.sqrt_nonneg (8 * a t)]
  have hs : ∀ t, Real.sqrt (8 * a (t + 1)) = Real.sqrt (8 * a t) + 4 := by
    intro t
    rw [ha t]
    have hsq := Real.sq_sqrt (by linarith [hnn t] : (0:ℝ) ≤ 8 * a t)
    have e : 8 * (a t + Real.sqrt (8 * a t) + 2) = (Real.sqrt (8 * a t) + 4) ^ 2 := by
      linear_combination (-1 : ℝ) * hsq
    rw [e, Real.sqrt_sq (by linarith [Real.sqrt_nonneg (8 * a t)])]
  have hlin : ∀ t : ℕ, Real.sqrt (8 * a t) = Real.sqrt (8 * a 0) + 4 * t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hs, ih]
      push_cast
      ring
  rw [hlin]
  have hlog : 0 ≤ Real.log (1 + 2 * (t:ℝ)) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ t := t.cast_nonneg; linarith)
  linarith
