-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_abs_productKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:05.626814+00:00
-- url     : https://prove2.me/submissions/4f9dc138-7c4b-4628-ada2-d269255ec06a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_abs_localKernel

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    (∑ τ, |productKernel size σ τ|) = ∏ p, localRow (size p) k (σ p) := by
  simp only [productKernel, Finset.abs_prod]
  rw [← Fintype.prod_sum (fun p (j : Option (Fin k)) =>
    |localKernel (size p) (σ p) j|)]
  simp_rw [sum_abs_localKernel (hsize _)]
end LongGapsBetweenPrimes
