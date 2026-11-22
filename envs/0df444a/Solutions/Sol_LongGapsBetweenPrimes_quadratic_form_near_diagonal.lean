-- Prove2me | solution 1 for LongGapsBetweenPrimes.quadratic_form_near_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:50.213249+00:00
-- url     : https://prove2.me/submissions/53bae0d6-4090-4527-baff-b3c193b1885e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_abs_quadratic_form_le_rows

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (ε : ℝ)
    (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1)
    (hrow : ∀ i, (∑ j, if j = i then 0 else |K i j|) ≤ ε) :
    |(∑ i, ∑ j, c i * c j * K i j) - ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by
  let L : ι → ι → ℝ := fun i j => if j = i then 0 else K i j
  have hL (i j : ι) : c i * c j * L i j =
      c i * c j * K i j - if j = i then c i ^ 2 else 0 := by
    by_cases hij : j = i <;> simp [L, hij, hdiag, pow_two]
  calc
    _ = |∑ i, ∑ j, c i * c j * L i j| := by
      simp_rw [hL, Finset.sum_sub_distrib]
      simp
    _ ≤ ∑ i, c i ^ 2 * ∑ j, |L i j| :=
      abs_quadratic_form_le_rows c L (by
        intro i j
        simp only [L, eq_comm, hsym i j])
    _ ≤ ∑ i, c i ^ 2 * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [L, apply_ite abs, abs_zero] using hrow i
    _ = _ := by rw [← Finset.sum_mul, mul_comm]
end LongGapsBetweenPrimes
