-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientRemainder_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:22.3438+00:00
-- url     : https://prove2.me/submissions/d23153e9-338a-4469-8a82-facd8abc2a86

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisorIndex

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P m : ℕ) (D : ℝ) :
    coefficientRemainder P m D =
      ∑ d : DivisorIndex P,
        if (d.val : ℝ) ≤ D / m ∧ d.val.Coprime m then
          coefficient P d.val / d.val.totient else 0 := by
  rw [coefficientRemainder, Finset.sum_filter]
  exact (sum_divisorIndex P _).symm
end LongGapsBetweenPrimes
