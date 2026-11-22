-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficient_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:52.160011+00:00
-- url     : https://prove2.me/submissions/9b9ea3a4-7ddd-4f92-a176-042a29f174d5

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_moment_tail_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} {v β : ℝ} (hv : 1 ≤ v) (hβ : 0 ≤ β) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => v < (d : ℝ)), |coefficient P d| / d.totient) ≤
      v ^ (-β) * coefficientAbsMoment P β := by
  classical
  have h1 : (1 : ℕ) ∉ P.divisors.filter (fun d : ℕ => v < (d : ℝ)) := by
    simp only [Finset.mem_filter, Nat.cast_one, not_and]
    exact fun _ => not_lt_of_ge hv
  simpa only [Finset.filter_erase, Finset.erase_eq_of_notMem h1,
    coefficientAbsMoment, div_mul_eq_mul_div] using
    moment_tail_le (P.divisors.erase 1) (fun d => |coefficient P d| / d.totient)
      (fun d => (d : ℝ)) v β (zero_lt_one.trans_le hv) hβ
      (fun d _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (fun d _ => Nat.cast_nonneg _)
end LongGapsBetweenPrimes
