-- Prove2me | solution 1 for Gilbreath.iterAbsDiff_shift_mul
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-25T14:11:15.192634+00:00
-- url     : https://prove2.me/submissions/441002ae-e88c-4c61-a91b-142c3693e009

import Definitions.Def_gilbreath_triangle

set_option autoImplicit false
open Gilbreath

theorem solution (a : ℕ → ℕ) (c s k n : ℕ) :
    iterAbsDiff (fun j => c * a (j + s)) k n =
      c * iterAbsDiff a k (n + s) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      change Int.natAbs
        ((iterAbsDiff (fun j => c * a (j + s)) k (n + 1) : ℤ) -
          (iterAbsDiff (fun j => c * a (j + s)) k n : ℤ)) =
        c * Int.natAbs
          ((iterAbsDiff a k (n + s + 1) : ℤ) - (iterAbsDiff a k (n + s) : ℤ))
      rw [ih, ih]
      have hi : n + 1 + s = n + s + 1 := by omega
      rw [hi]
      simp only [Nat.cast_mul, ← mul_sub, Int.natAbs_mul, Int.natAbs_natCast]

#print axioms solution
