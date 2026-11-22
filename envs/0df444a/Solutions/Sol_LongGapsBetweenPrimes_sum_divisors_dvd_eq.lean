-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_divisors_dvd_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:10.334397+00:00
-- url     : https://prove2.me/submissions/51de1c1a-8928-4cfd-bc4f-7153e511ef5f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P p : ℕ} (hP : P ≠ 0) (hp : 0 < p) (hpP : p ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), f d) =
      ∑ e ∈ (P / p).divisors, f (p * e) := by
  symm
  refine Finset.sum_bij (fun e _ => p * e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e he
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr
        ⟨(Nat.dvd_div_iff_mul_dvd hpP).mp (Nat.dvd_of_mem_divisors he), hP⟩,
        dvd_mul_right p e⟩
  · intro e₁ _ e₂ _ h
    exact Nat.mul_left_cancel hp h
  · intro d hd
    obtain ⟨hd, hpd⟩ := Finset.mem_filter.mp hd
    refine ⟨d / p, Nat.mem_divisors.mpr ⟨?_, ?_⟩, Nat.mul_div_cancel' hpd⟩
    · exact Nat.div_dvd_div hpd (Nat.dvd_of_mem_divisors hd)
    · intro h
      apply hP
      rw [← Nat.mul_div_cancel' hpP, h, mul_zero]
end LongGapsBetweenPrimes
