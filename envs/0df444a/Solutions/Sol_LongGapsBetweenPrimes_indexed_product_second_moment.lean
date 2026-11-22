-- Prove2me | solution 1 for LongGapsBetweenPrimes.indexed_product_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:54.810421+00:00
-- url     : https://prove2.me/submissions/a1bf1b29-9430-44a2-8792-3c4c8a91d654

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_quadratic_form_near_diagonal
import Theorems.Thm_LongGapsBetweenPrimes_productKernel_symm
import Theorems.Thm_LongGapsBetweenPrimes_productKernel_diag
import Theorems.Thm_LongGapsBetweenPrimes_sum_abs_productKernel
import Theorems.Thm_LongGapsBetweenPrimes_average_productBasis_localBasis
import Theorems.Thm_LongGapsBetweenPrimes_indexed_offdiag_sum_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → α → Option (Fin k)) (hσ : Function.Injective σ) (c : ι → ℝ) (ε : ℝ)
    (hbound : ∀ i, (∏ p, localRow (size p) k (σ i p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t =>
        (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) -
      ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by
  classical
  have hmoment : Finset.expect Finset.univ (fun t =>
      (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) =
      ∑ i, ∑ j, c i * c j * productKernel size (σ i) (σ j) := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    simp_rw [Finset.expect_sum_comm]
    simp_rw [mul_mul_mul_comm (c _) _ (c _) _, ← Finset.mul_expect,
      average_productBasis_localBasis size hsize root hroot]
  rw [hmoment]
  apply quadratic_form_near_diagonal c (fun i j => productKernel size (σ i) (σ j)) ε
    (fun i j => productKernel_symm size (σ i) (σ j))
    (fun i => productKernel_diag size (σ i))
  intro i
  exact (indexed_offdiag_sum_le σ hσ (productKernel size)
    (productKernel_diag size) i).trans (by simpa [sum_abs_productKernel size hsize] using hbound i)
end LongGapsBetweenPrimes
