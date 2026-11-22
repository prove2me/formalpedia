-- Prove2me | solution 1 for LongGapsBetweenPrimes.moment_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:00.408796+00:00
-- url     : https://prove2.me/submissions/c6995591-d968-4d8b-a455-ee01ef27ac3d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} (s : Finset α) (f v : α → ℝ) (D β : ℝ)
    (hD : 0 < D) (hβ : 0 ≤ β) (hf : ∀ a ∈ s, 0 ≤ f a)
    (hv : ∀ a ∈ s, 0 ≤ v a) :
    (∑ a ∈ s.filter (fun a => D < v a), f a) ≤
      D ^ (-β) * ∑ a ∈ s, f a * (v a) ^ β := by
  rw [Real.rpow_neg hD.le, ← div_eq_inv_mul]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hD β)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ a ∈ s.filter (fun a => D < v a), f a * (v a) ^ β := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨has, hav⟩ := Finset.mem_filter.mp ha
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hD.le hav.le hβ) (hf a has)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a ha _ => mul_nonneg (hf a ha) (Real.rpow_nonneg (hv a ha) _))
end LongGapsBetweenPrimes
