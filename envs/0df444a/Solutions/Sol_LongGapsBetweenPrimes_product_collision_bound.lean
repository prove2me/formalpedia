-- Prove2me | solution 1 for LongGapsBetweenPrimes.product_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:37.430213+00:00
-- url     : https://prove2.me/submissions/f70b48d4-7852-4e90-abcf-f70435309169

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_weighted_union_bound
import Theorems.Thm_LongGapsBetweenPrimes_sum_pair_marked_product

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α Ω : Type*} [Fintype α] [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ d, 0 ≤ w d) (hsum : ∑ d, w d = 1)
    (mark : α → Ω → Prop) [∀ p, DecidablePred (mark p)] (k : ℕ) :
    (∑ r : Fin k → Ω, (∏ i, w (r i)) *
      if ∃ p i j, i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0) ≤
        (k : ℝ) ^ 2 * ∑ p, (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by
  classical
  have h := weighted_union_bound
    (fun r : Fin k → Ω => ∏ i, w (r i))
    (fun (x : α × Fin k × Fin k) r =>
      x.2.1 ≠ x.2.2 ∧ mark x.1 (r x.2.1) ∧ mark x.1 (r x.2.2))
    (fun r => Finset.prod_nonneg fun i _ => hw (r i))
  calc
    _ ≤ ∑ p, ∑ i : Fin k, ∑ j : Fin k,
        ∑ r : Fin k → Ω, (∏ ℓ, w (r ℓ)) *
          if i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0 := by
      simpa only [Prod.exists, Fintype.sum_prod_type] using h
    _ ≤ ∑ p, ∑ _i : Fin k, ∑ _j : Fin k,
        (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp [hij, sq_nonneg]
      · simpa only [hij, ne_eq, not_false_eq_true, true_and] using
          (sum_pair_marked_product w hsum (mark p) i j hij).le
    _ = _ := by simp [Finset.mul_sum, pow_two, mul_assoc]
end LongGapsBetweenPrimes
