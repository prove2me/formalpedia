-- Prove2me | solution 1 for LongGapsBetweenPrimes.prod_primeIndex_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:23.36152+00:00
-- url     : https://prove2.me/submissions/ac676974-f28b-411c-b567-29acf10a743c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ p : PrimeIndex P, if p.val ∣ d then f p.val else 1) = ∏ p ∈ d.primeFactors, f p := by
  classical
  have h := Finset.prod_attach P.primeFactors (fun p => if p ∣ d then f p else 1)
  simp only [Finset.attach_eq_univ] at h
  rw [h, ← Finset.prod_filter, Nat.primeFactors_filter_dvd_of_dvd hP hd]
end LongGapsBetweenPrimes
