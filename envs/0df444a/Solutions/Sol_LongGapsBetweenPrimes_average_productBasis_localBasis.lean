-- Prove2me | solution 1 for LongGapsBetweenPrimes.average_productBasis_localBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:14.288833+00:00
-- url     : https://prove2.me/submissions/31712932-5be9-430c-8b3e-85f2f3521b4c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_average_localBasis_mul

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ τ : α → Option (Fin k)) :
    Finset.expect Finset.univ (fun t => productBasis (fun p => localBasis (root p)) σ t *
      productBasis (fun p => localBasis (root p)) τ t) = productKernel size σ τ := by
  classical
  simp only [productBasis, ← Finset.prod_mul_distrib]
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_pi,
    Nat.cast_prod, ← Fintype.prod_sum (fun p t =>
      localBasis (root p) (σ p) t * localBasis (root p) (τ p) t),
    ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun p _ =>
    (Finset.expect_eq_sum_div_card _ _).symm.trans
      (average_localBasis_mul (hsize p) (root p) (hroot p) (σ p) (τ p))
end LongGapsBetweenPrimes
