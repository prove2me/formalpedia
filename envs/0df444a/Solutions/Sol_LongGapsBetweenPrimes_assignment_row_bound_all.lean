-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignment_row_bound_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:23.230008+00:00
-- url     : https://prove2.me/submissions/71d4a230-a385-4db0-95f6-78ab33506fe8

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignment_row_bound

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (σ : α → Option (Fin k))
    {M D : ℝ} (hM : 1 < M) (hsize : ∀ p, M ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) := by
  cases k with
  | zero =>
      have hσ (p : α) : σ p = none := Subsingleton.elim _ _
      simp [hσ, localRow]
  | succ k =>
      exact assignment_row_bound size (Nat.succ_pos k) σ hM hsize hcut
end LongGapsBetweenPrimes
