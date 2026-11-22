-- Prove2me | solution 1 for LongGapsBetweenPrimes.mod_invariant_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:36.022522+00:00
-- url     : https://prove2.me/submissions/58b02cf5-8ae0-4187-b981-1ca99394b5ef

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m n : ℕ} (hmn : m ∣ n) (f : ℕ → ℝ)
    (hf : ∀ a, f (a % m) = f a) : ∀ a, f (a % n) = f a := by
  intro a
  rw [← hf (a % n), Nat.mod_mod_of_dvd a hmn, hf]
end LongGapsBetweenPrimes
