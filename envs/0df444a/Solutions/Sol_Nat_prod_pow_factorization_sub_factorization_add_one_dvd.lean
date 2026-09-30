-- Prove2me | solution 1 for Nat.prod_pow_factorization_sub_factorization_add_one_dvd
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:44.28054+00:00
-- url     : https://prove2.me/submissions/09381685-c3fd-4b5e-a2ce-28ae5ecf7dde

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The prime powers that decide whether a divisor fits beside a fixed factor

Let `f` and `d` both divide `h`. Whether the product `f * d` still divides `h` is decided one
prime at a time, and only at the primes of `f`: room for `f * d` fails at `p` exactly when `d`
carries `p` to a power that exceeds the room `h` leaves after `f`, which is `v_p h - v_p f`. So
`f * d ∣ h` holds exactly when no prime `p` of `f` divides `d` to the exponent
`v_p h - v_p f + 1`.

The one-sided reading is what makes the statement useful: the primes outside `f` impose no
condition, because `d ∣ h` already leaves them enough room.

The exponents `v_p h - v_p f + 1` are themselves exponents of prime powers dividing `h`, both
one prime at a time and all at once, since the primes of `f` are distinct.

## Main results

* `Nat.mul_dvd_iff_forall_not_pow_dvd`: `f * d ∣ h` as non-divisibility of `d` by a
  prime power at each prime of `f`.
* `Nat.pow_factorization_sub_factorization_add_one_dvd`: the tested prime power divides `h`.
* `Nat.prod_pow_factorization_sub_factorization_add_one_dvd`: so does their product over the
  primes of `f`.
-/

 section

namespace Nat
end Nat
section Nat
open Nat

open Finset



/-- **The prime power tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.** For `f`
dividing `h` and `p` a prime of `f`, the exponent `v_p h - v_p f + 1` does not exceed `v_p h`,
because `f` contributes at least one power of `p`. -/
theorem Nat.pow_factorization_sub_factorization_add_one_dvd {f h : ℕ} (hf : f ∣ h) {p : ℕ}
    (hp : p ∈ f.primeFactors) :
    p ^ (h.factorization p - f.factorization p + 1) ∣ h := by
  rcases _root_.eq_or_ne h 0 with rfl | hh
  · exact _root_.dvd_zero _
  have hprime := _root_.Nat.prime_of_mem_primeFactors hp
  have hf0 : f ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hpos : 0 < f.factorization p :=
    hprime.factorization_pos_of_dvd hf0 (_root_.Nat.dvd_of_mem_primeFactors hp)
  have hle : f.factorization p ≤ h.factorization p := (_root_.Nat.factorization_le_iff_dvd hf0 hh).mpr hf p
  refine (hprime.pow_dvd_iff_le_factorization hh).mpr ?_
  omega

/-- **The product of the prime powers tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.**
The primes of `f` are distinct, so the prime powers `p ^ (v_p h - v_p f + 1)` occur at distinct
primes and their product still divides `h`: it is the product of prime powers read off a finitely
supported exponent function bounded by the factorization of `h`. -/
theorem solution {f h : ℕ} (hf : f ∣ h) :
    (∏ p ∈ f.primeFactors, p ^ (h.factorization p - f.factorization p + 1)) ∣ h := by
  classical
  rcases _root_.eq_or_ne h 0 with rfl | hh
  · exact _root_.dvd_zero _
  rw [← _root_.Finsupp.prod_indicator_index (fun p => h.factorization p - f.factorization p + 1)
    (h := (· ^ ·)) fun _ _ => _root_.pow_zero _]
  refine _root_.Nat.prod_pow_dvd_of_le_factorization fun p => ?_
  rw [_root_.Finsupp.indicator_apply]
  split_ifs with hp
  · exact ((_root_.Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hh).mp
      (_root_.Nat.pow_factorization_sub_factorization_add_one_dvd hf hp)
  · exact _root_.Nat.zero_le _

end Nat

end
end
