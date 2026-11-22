-- Prove2me | solution 1 for LongGapsBetweenPrimes.partial_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:11.774251+00:00
-- url     : https://prove2.me/submissions/4030fcc3-4777-48c7-9c01-f4b64d29f114

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_one_lt_of_mem_divisors_erase_one
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_neg
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_cancellation

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ P.divisors) (h1 : 1 ∈ E) :
    ∑ d ∈ E, coefficient P d / d.totient =
      ∑ d ∈ P.divisors \ E, |coefficient P d| / d.totient := by
  have hsum := Finset.sum_sdiff hE (f := fun d => coefficient P d / d.totient)
  rw [coefficient_cancellation hP] at hsum
  rw [eq_neg_of_add_eq_zero_right hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rcases Finset.mem_sdiff.mp hd with ⟨hd, hdE⟩
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdE h1
  rw [abs_of_neg (coefficient_neg hP
    (one_lt_of_mem_divisors_erase_one (Finset.mem_erase.mpr ⟨hd1, hd⟩))), neg_div]
end LongGapsBetweenPrimes
