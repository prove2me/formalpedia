-- Prove2me | solution 1 for IsCyclic.le_card_filter_dvd_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:48:21.424134+00:00
-- url     : https://prove2.me/submissions/67aa5884-6e95-482f-8b8f-16bd0d187222

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Theorems.Thm_IsCyclic_card_filter_dvd_orderOf_eq_mul_prod_primeFactors

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting the elements of a cyclic group by a condition on their order

In a finite cyclic group, the number of elements whose order satisfies a predicate `p` is the sum
of `φ d` over the divisors `d` of the group order that satisfy `p`.

Mathlib counts elements of an *exact* order: `IsCyclic.card_orderOf_eq_totient` says there are
`φ d` of them for each `d` dividing the group order. Summing that over the divisors selected by
`p` is the whole content here.

The point of stating it for a predicate is that it turns a count defined by a condition on orders
into an arithmetic sum over divisors, where the group has disappeared. Whatever `p` is, the answer
is a totient sum over `{d ∣ #α | p d}`, so it can then be evaluated or estimated by number theory
alone.

## Main results

* `IsCyclic.card_filter_orderOf_eq_sum_totient`, and its additive counterpart: the count of
  elements whose order satisfies `p` is `∑ φ d` over the divisors `d` of the group order with
  `p d`.
* `IsCyclic.card_filter_dvd_orderOf_eq_sum_totient`: the case `p = (f ∣ ·)`.
* `IsCyclic.card_filter_dvd_orderOf_mul_prod_primeFactors`, and its additive counterpart: that
  case in closed form, in `ℕ`.
* `IsCyclic.card_filter_dvd_orderOf_eq_mul_prod_primeFactors`, and its additive counterpart: the
  closed form as a product over `ℚ`.
* `IsCyclic.le_card_filter_dvd_orderOf`, and its additive counterpart: the uniform lower bound
  `(1 - 2 ^ -r) ^ #f.primeFactors` for the proportion of elements of order divisible by `f`, when
  `f ^ r ∣ #α`.

## The elements of order divisible by `f`, in closed form

Let `α` have order `h` and let `f` divide `h`. The elements of `α` whose order is a multiple of
`f` are counted exactly:

`#{τ | f ∣ orderOf τ} = h * ∏ p ∣ f, (1 - p ^ -(v_p h - v_p f + 1))`,

the product running over the primes of `f`. Writing `τ = g ^ k` for a generator `g`, `f` divides
the order of `τ` exactly when `p ^ (v_p h - v_p f + 1)` fails to divide `k` for every prime `p` of
`f` (`IsOfFinOrder.dvd_orderOf_pow_iff`). Those conditions constrain `k` modulo coprime prime
powers, so they are independent and the count is a product.

Two forms of the count are recorded: an identity in `ℕ`, cleared of denominators, and the
displayed product over `ℚ`. At `f = h` every exponent is `1` and the count becomes Euler's
product formula `Nat.totient_mul_prod_primeFactors`, since the elements whose order is a multiple
of `h` are the `φ h` generators.

The third result is the estimate that makes the count usable when `f` is fixed and `h` is
divisible by a high power of `f`: if `f ^ r ∣ h` with `1 ≤ r`, every factor of the product is at
least `1 - 2 ^ -r`, so the proportion of elements of order divisible by `f` is at least
`(1 - 2 ^ -r) ^ #f.primeFactors`, which tends to `1` as `r` grows.
-/

 section

open Finset Nat

open scoped Function -- for the `on` notation in `Pairwise (Nat.Coprime on a)`

variable {α : Type*} [Group α] [Fintype α] [IsCyclic α]





namespace IsCyclic
end IsCyclic
section IsCyclic
open IsCyclic

variable {f : ℕ}







/-- **A uniform lower bound for the elements of order divisible by `f`.** If the order of the
cyclic group is divisible by `f ^ r` with `1 ≤ r`, then at least a proportion
`(1 - 2 ^ -r) ^ #f.primeFactors` of its elements have order divisible by `f`.

Each factor of `card_filter_dvd_orderOf_eq_mul_prod_primeFactors` is bounded below by `1 - 2 ^ -r`
because `f ^ r ∣ h` forces the exponent `v_p h - v_p f + 1` to be at least `r` at every prime `p`
of `f`, and `p` is at least `2`. The bound depends on `f` only through its number of prime
factors, so it tends to `1` as `r` grows. -/

theorem solution {r : ℕ} (hr : 1 ≤ r) (hfr : f ^ r ∣ _root_.Fintype.card α) :
    (1 - (2 : ℚ)⁻¹ ^ r) ^ f.primeFactors.card * _root_.Fintype.card α
      ≤ #{τ : α | f ∣ _root_.orderOf τ} := by
  have hf : f ∣ _root_.Fintype.card α := (_root_.dvd_pow_self f (by omega)).trans hfr
  have hf0 : f ≠ 0 := fun h0 => _root_.Fintype.card_ne_zero (zero_dvd_iff.mp (h0 ▸ hf))
  rw [_root_.IsCyclic.card_filter_dvd_orderOf_eq_mul_prod_primeFactors hf, _root_.mul_comm (_root_.Fintype.card α : ℚ)]
  refine _root_.mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← _root_.Finset.prod_const]
  refine _root_.Finset.prod_le_prod (fun p _ => ?_) fun p hp => ?_
  · have : (2 : ℚ)⁻¹ ^ r ≤ 1 := _root_.pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · -- the exponent at `p` is at least `r`, and `2 ≤ p`
    have hprime := _root_.Nat.prime_of_mem_primeFactors hp
    have hpos : 0 < f.factorization p :=
      hprime.factorization_pos_of_dvd hf0 (_root_.Nat.dvd_of_mem_primeFactors hp)
    have hle : r * f.factorization p ≤ (_root_.Fintype.card α).factorization p := by
      have := (_root_.Nat.factorization_le_iff_dvd (_root_.pow_ne_zero r hf0) _root_.Fintype.card_ne_zero).mpr hfr p
      rwa [_root_.Nat.factorization_pow, _root_.Finsupp.smul_apply, _root_.smul_eq_mul] at this
    have hre : r ≤ (_root_.Fintype.card α).factorization p - f.factorization p + 1 := by
      have h1 : r - 1 ≤ (r - 1) * f.factorization p := _root_.Nat.le_mul_of_pos_right _ hpos
      have h2 : (r - 1) * f.factorization p + f.factorization p = r * f.factorization p := by
        cases r with
        | zero => omega
        | succ n => simp [_root_.Nat.succ_mul]
      omega
    have h2p : (2 : ℚ) ^ r ≤ (p : ℚ) ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) :=
      calc (2 : ℚ) ^ r
          ≤ (2 : ℚ) ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) :=
            _root_.pow_le_pow_right₀ (by norm_num) hre
        _ ≤ (p : ℚ) ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) :=
            _root_.pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hprime.two_le) _
    have hinv : ((p : ℚ) ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1))⁻¹
        ≤ (2 : ℚ)⁻¹ ^ r := by
      rw [_root_.inv_pow]
      exact _root_.inv_anti₀ (by positivity) h2p
    linarith

end IsCyclic

end
end
