-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_zero_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:20.489397+00:00
-- url     : https://prove2.me/submissions/53fdf4b2-a614-4ac5-a2d2-e9a82f29bb8d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_primeProduct
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_euler_factorization

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 * eulerProduct Z 1 = eulerProduct Y 1 := by
  rw [auxiliaryProduct, divisorEulerMoment_primeProduct _
    (fun _ hp => auxiliaryPrimes_prime hp)]
  convert auxiliary_euler_factorization hZY (1 : ℝ) using 2
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (auxiliaryPrimes_prime hp).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (auxiliaryPrimes_prime hp).ne_one)
  simp only [Real.rpow_zero, Real.rpow_neg_one]
  field_simp
  ring
end LongGapsBetweenPrimes
