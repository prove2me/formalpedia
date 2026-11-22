-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficient_noncoprime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:21.765391+00:00
-- url     : https://prove2.me/submissions/c3c12c49-cb19-4171-8e20-33d8d02544a5

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_prime_incidence

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P m : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hm : m ∣ P) (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient) ≤
      ∑ p ∈ m.primeFactors, 4 / (p : ℝ) := by
  classical
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hsq.ne_zero (by simpa using hm)
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ p ∈ m.primeFactors,
        if p ∣ d then |coefficient P d| / d.totient else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro d _
      by_cases hdm : ¬d.Coprime m
      · rw [if_pos hdm]
        obtain ⟨p, hp, hpd, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hdm
        have h := Finset.single_le_sum
          (f := fun p => if p ∣ d then |coefficient P d| / d.totient else 0)
          (fun p _ => by split_ifs <;> positivity) (hp.mem_primeFactors hpm hm0)
        simpa only [if_pos hpd] using h
      · rw [if_neg hdm]
        positivity
    _ = ∑ p ∈ m.primeFactors,
        ∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hm
      exact coefficient_prime_incidence hP hsq (Nat.prime_of_mem_primeFactors hp) hpP
        (hcoeff p (Nat.mem_divisors.mpr ⟨hpP, hsq.ne_zero⟩))
end LongGapsBetweenPrimes
