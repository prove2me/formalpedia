-- Prove2me | solution 1 for LongGapsBetweenPrimes.prime_coordinate_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:59.619293+00:00
-- url     : https://prove2.me/submissions/bcfef451-0708-4ed1-8259-83fa6f1f2d41

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k p : ℕ} (hp : p.Prime) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    {i j : Fin k} (hi : p ∣ (r i).val) (hj : p ∣ (r j).val) : i = j := by
  by_contra hij
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hi, hj⟩) (hpair i j hij)
end LongGapsBetweenPrimes
