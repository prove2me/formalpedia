-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_ge_eulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:44.39516+00:00
-- url     : https://prove2.me/submissions/6d624dc8-3412-4552-97d1-12f38e86df93

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_primeProduct
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_pos
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_euler_factorization
import Theorems.Thm_LongGapsBetweenPrimes_squarefree_euler_factor_ge

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) {t : ℝ} (ht : 0 < t) :
    eulerProduct Y (1 + t) ≤
      divisorEulerMoment (auxiliaryProduct Z Y) (-t) * eulerProduct Z (1 + t) := by
  classical
  rw [← auxiliary_euler_factorization hZY (1 + t)]
  apply mul_le_mul_of_nonneg_right _ (eulerProduct_pos Z (by linarith)).le
  rw [auxiliaryProduct, divisorEulerMoment_primeProduct _
    (fun _ hp => auxiliaryPrimes_prime hp)]
  apply Finset.prod_le_prod
  · intro p hp
    exact (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt) (by linarith)))).le
  · intro p hp
    exact squarefree_euler_factor_ge
      (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt) ht
end LongGapsBetweenPrimes
