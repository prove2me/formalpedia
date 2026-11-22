-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentNormalizer_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:13.834795+00:00
-- url     : https://prove2.me/submissions/e772262f-c7f7-4f05-ab54-0ca8815ef8e0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    assignmentNormalizer size σ ^ 2 = assignmentVariance size σ := by
  unfold assignmentNormalizer assignmentVariance
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  have hp : (1 : ℝ) ≤ size p := by exact_mod_cast (hsize p).le
  cases σ p <;> simp [inv_pow, Real.sq_sqrt (sub_nonneg.mpr hp), one_div]
end LongGapsBetweenPrimes
