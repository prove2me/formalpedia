-- Prove2me | solution 1 for Nat.mul_dvd_iff_forall_not_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:42.505701+00:00
-- url     : https://prove2.me/submissions/3e01db08-3317-4aaa-bd8b-1af8de34adc3

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

/-- **A divisor fits beside a fixed factor exactly away from prime powers.** For `f` and `d`
dividing a nonzero `h`, the product `f * d` divides `h` if and only if no prime `p` of `f`
divides `d` to the exponent `v_p h - v_p f + 1`.

Only the primes of `f` are tested: at a prime `p` not dividing `f` the hypothesis `d ∣ h`
already gives `v_p d ≤ v_p h`. -/
theorem solution {f d h : ℕ} (hh : h ≠ 0) (hf : f ∣ h) (hd : d ∣ h) :
    f * d ∣ h ↔
      ∀ p ∈ f.primeFactors, ¬p ^ (h.factorization p - f.factorization p + 1) ∣ d := by
  have hf0 : f ≠ 0 := fun h0 => hh (zero_dvd_iff.mp (h0 ▸ hf))
  have hd0 : d ≠ 0 := fun h0 => hh (zero_dvd_iff.mp (h0 ▸ hd))
  have hfh : ∀ p, f.factorization p ≤ h.factorization p :=
    fun p => (_root_.Nat.factorization_le_iff_dvd hf0 hh).mpr hf p
  have hdh : ∀ p, d.factorization p ≤ h.factorization p :=
    fun p => (_root_.Nat.factorization_le_iff_dvd hd0 hh).mpr hd p
  rw [← _root_.Nat.factorization_le_iff_dvd (_root_.Nat.mul_ne_zero hf0 hd0) hh, _root_.Finsupp.le_def,
    _root_.Nat.factorization_mul hf0 hd0]
  simp only [_root_.Finsupp.coe_add, _root_.Pi.add_apply]
  constructor
  · intro hle p hp hdvd
    have hb : 0 < f.factorization p :=
      (_root_.Nat.Prime.factorization_pos_of_dvd (_root_.Nat.prime_of_mem_primeFactors hp) hf0
        (_root_.Nat.dvd_of_mem_primeFactors hp))
    have := ((_root_.Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hd0).mp hdvd
    have := hle p
    have := hfh p
    omega
  · intro hp p
    by_cases hmem : p ∈ f.primeFactors
    · have hb : 0 < f.factorization p :=
        (_root_.Nat.Prime.factorization_pos_of_dvd (_root_.Nat.prime_of_mem_primeFactors hmem) hf0
          (_root_.Nat.dvd_of_mem_primeFactors hmem))
      have hlt : ¬(h.factorization p - f.factorization p + 1 ≤ d.factorization p) :=
        fun hle => hp p hmem
          (((_root_.Nat.prime_of_mem_primeFactors hmem).pow_dvd_iff_le_factorization hd0).mpr hle)
      have := hfh p
      omega
    · have : f.factorization p = 0 := by
        rw [← _root_.Nat.support_factorization] at hmem
        exact Finsupp.notMem_support_iff.mp hmem
      have := hdh p
      omega





end Nat

end
end
