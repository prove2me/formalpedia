-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentNormalizer_mul_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:49.548148+00:00
-- url     : https://prove2.me/submissions/45ffe718-1805-4864-a0da-6c6025ab3a4c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (root : (p : α) → Fin k → Fin (size p))
    (σ : α → Option (Fin k)) (t : (p : α) → Fin (size p)) :
    assignmentNormalizer size σ * productBasis (fun p => localBasis (root p)) σ t =
      productBasis (fun p => rawLocalBasis (root p)) σ t := by
  unfold assignmentNormalizer productBasis
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hp : Real.sqrt ((size p : ℝ) - 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (by exact_mod_cast hsize p)))
  cases σ p <;> simp [localBasis, rawLocalBasis, hp]
end LongGapsBetweenPrimes
