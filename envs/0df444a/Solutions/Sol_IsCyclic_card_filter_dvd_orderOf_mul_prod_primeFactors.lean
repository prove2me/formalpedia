-- Prove2me | solution 1 for IsCyclic.card_filter_dvd_orderOf_mul_prod_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:23:33.904759+00:00
-- url     : https://prove2.me/submissions/64b715b9-9768-4247-b9cf-1853b8a92628

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
import Theorems.Thm_Nat_mul_dvd_iff_forall_not_pow_dvd
import Theorems.Thm_Nat_prod_pow_factorization_sub_factorization_add_one_dvd

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

open Finset



/-- **The prime power tested by `mul_dvd_iff_forall_not_pow_dvd` divides `h`.** For `f`
dividing `h` and `p` a prime of `f`, the exponent `v_p h - v_p f + 1` does not exceed `v_p h`,
because `f` contributes at least one power of `p`. -/
theorem pow_factorization_sub_factorization_add_one_dvd {f h : ℕ} (hf : f ∣ h) {p : ℕ}
    (hp : p ∈ f.primeFactors) :
    p ^ (h.factorization p - f.factorization p + 1) ∣ h := by
  rcases eq_or_ne h 0 with rfl | hh
  · exact dvd_zero _
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hf0 : f ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hpos : 0 < f.factorization p :=
    hprime.factorization_pos_of_dvd hf0 (Nat.dvd_of_mem_primeFactors hp)
  have hle : f.factorization p ≤ h.factorization p := (Nat.factorization_le_iff_dvd hf0 hh).mpr hf p
  refine (hprime.pow_dvd_iff_le_factorization hh).mpr ?_
  omega



end Nat

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting residues by a condition on their reduction

A condition on `x : ZMod n` that only reads the reduction of `x` modulo a divisor of `n` can be
counted after reducing. This file records the two counting laws that result.

Reducing along a single divisor `m ∣ n` multiplies the count: the reduction `ZMod n → ZMod m`,
written here as `fun x ↦ (x.val : ZMod m)`, is a surjective additive homomorphism, so all of its
fibres have the same size and a condition pulled back along it holds proportionally often. The
identity is stated as `m * (count over ZMod n) = n * (count over ZMod m)`, which carries the same
information as a division by `m` without a quotient appearing.

Splitting a modulus into pairwise coprime factors multiplies the counts: conditions imposed on
the separate factors are independent, so the number of residues satisfying all of them is the
product of the individual counts. This is the Chinese remainder theorem `ZMod.prodEquivPi` in
counting form.

## Main results

* `ZMod.mul_card_filter_natCast_val`: counting a condition on the reduction modulo `m ∣ n`.
* `ZMod.card_filter_forall_natCast_val`: counting independent conditions on coprime factors.
* `ZMod.card_filter_not_self_dvd_val`: the residues whose representative the modulus does not
  divide, the base case of such a count.
-/

 section

open Finset

open scoped Function -- for the `on` notation in `Pairwise (Nat.Coprime on a)`

namespace ZMod

variable {m n : ℕ}

/-- The residues modulo `n` satisfying a condition on their reduction modulo `m ∣ n` are as many
as the residues modulo `m` satisfying it, times the common size of a fibre of the reduction. -/
private theorem card_filter_natCast_val_eq_mul_card_fiber [NeZero m] [NeZero n] (hmn : m ∣ n)
    (Q : ZMod m → Prop) [DecidablePred Q] :
    #{x : ZMod n | Q (x.val : ZMod m)}
      = #{y : ZMod m | Q y} * #{x : ZMod n | (x.val : ZMod m) = 0} := by
  have hval : ∀ x : ZMod n, ((x.val : ZMod m)) = castHom hmn (ZMod m) x := fun x => by
    rw [castHom_apply, natCast_val]
  have hsurj : Function.Surjective (castHom hmn (ZMod m)) := castHom_surjective hmn
  simp only [hval]
  have hfib : ∀ y : ZMod m, #{x : ZMod n | castHom hmn (ZMod m) x = y}
      = #{x : ZMod n | castHom hmn (ZMod m) x = 0} := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range (castHom hmn (ZMod m)) (hsurj y) (hsurj 0)
  -- split the count into the fibres over the residues modulo `m` satisfying `Q`; the hole left
  -- by `Finset.sum_congr` is the identification of each of those fibres with the fibre over `0`
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod n => castHom hmn (ZMod m) x)
      (t := {y : ZMod m | Q y})
      (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩),
    Finset.sum_congr rfl fun y hy => ?_, Finset.sum_const, smul_eq_mul]
  have hy' : Q y := (Finset.mem_filter.mp hy).2
  rw [← hfib y]
  refine congrArg Finset.card (Finset.ext fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hy', h⟩⟩

/-- **Counting a condition on the reduction modulo a divisor.** For `m ∣ n`, the residues modulo
`n` whose reduction modulo `m` satisfies `Q` are `n / m` times as many as the residues modulo `m`
satisfying `Q`, stated without the quotient. -/
theorem mul_card_filter_natCast_val [NeZero m] [NeZero n] (hmn : m ∣ n)
    (Q : ZMod m → Prop) [DecidablePred Q] :
    m * #{x : ZMod n | Q (x.val : ZMod m)} = n * #{y : ZMod m | Q y} := by
  have h2 := card_filter_natCast_val_eq_mul_card_fiber hmn (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ, ZMod.card] at h2
  rw [card_filter_natCast_val_eq_mul_card_fiber hmn Q]
  calc m * (#{y : ZMod m | Q y} * #{x : ZMod n | (x.val : ZMod m) = 0})
      = m * #{x : ZMod n | (x.val : ZMod m) = 0} * #{y : ZMod m | Q y} := by ring
    _ = n * #{y : ZMod m | Q y} := by rw [← h2]

/-- **All residues but zero have a representative the modulus does not divide.** A representative
is smaller than the modulus, so the modulus divides it exactly when it vanishes. -/
@[simp]
theorem card_filter_not_self_dvd_val [NeZero m] : #{z : ZMod m | ¬m ∣ z.val} = m - 1 := by
  have hzero : ∀ z : ZMod m, m ∣ z.val ↔ z = 0 := fun z =>
    ⟨fun hdvd => (ZMod.val_eq_zero z).mp (Nat.eq_zero_of_dvd_of_lt hdvd z.val_lt),
      fun h => by simp [h]⟩
  have herase : ({z : ZMod m | ¬m ∣ z.val} : Finset (ZMod m)) = Finset.univ.erase 0 := by
    ext z
    simp [hzero, Finset.mem_erase]
  rw [herase, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]

/-- **Counting independent conditions on coprime factors.** If the moduli `a i` are pairwise
coprime, the residues modulo `∏ i, a i` whose reduction modulo each `a i` satisfies `Q i` are
counted by the product over `i` of the residues modulo `a i` satisfying `Q i`. -/
theorem card_filter_forall_natCast_val {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (Q : ∀ i, ZMod (a i) → Prop) [∀ i, DecidablePred (Q i)] :
    #{x : ZMod (∏ i, a i) | ∀ i, Q i (x.val : ZMod (a i))}
      = ∏ i, #{y : ZMod (a i) | Q i y} := by
  classical
  have hval : ∀ (x : ZMod (∏ i, a i)) (i : ι),
      ((x.val : ZMod (a i))) = prodEquivPi a hcop x i := fun x i => by
    rw [prodEquivPi_apply, castHom_apply, natCast_val]
  have e : {x : ZMod (∏ i, a i) // ∀ i, Q i (x.val : ZMod (a i))} ≃
      ∀ i, {y : ZMod (a i) // Q i y} :=
    ((prodEquivPi a hcop).toEquiv.subtypeEquiv fun x => by simp only [hval]; rfl).trans
      Equiv.subtypePiEquivPi
  simpa only [Fintype.card_subtype, Fintype.card_pi] using Fintype.card_congr e

end ZMod

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Orders of elements and cardinalities

Let `g` have finite order `n` and let `f` divide `n`. The order of `g ^ k` is `n / gcd n k`, so
`f` divides it exactly when `f * gcd n k` divides `n`. That condition is decided one prime of `f`
at a time: it fails at `p` exactly when `k` is divisible by `p ^ (v_p n - v_p f + 1)`, the room
`n` leaves at `p` after `f`, plus one.

In a finite additive group with one, the cardinality casts to `0`, as Mathlib's
`Nat.cast_card_eq_zero` records, so the cardinality minus one casts to `-1`.

## Main results

* `IsOfFinOrder.dvd_orderOf_pow_iff`, and its additive counterpart: divisibility of the order of
  a power as non-divisibility of its exponent by a prime power at each prime of `f`.
* `TauCeti.natCast_natCard_sub_one_eq_neg_one`: in a finite additive group with one of
  cardinality `q`, the cast of `q - 1` is `-1`, a companion of Mathlib's `Nat.cast_card_eq_zero`.
-/

 section

namespace IsOfFinOrder

variable {G : Type*} [Monoid G]

/-- **When a number divides the order of a power.** Let `g` have finite order and let `f` divide
that order. Then `f` divides the order of `g ^ k` exactly when, for every prime `p` of `f`, the
exponent `k` is not divisible by `p ^ (v_p (orderOf g) - v_p f + 1)`.

The exponent is the room `orderOf g` leaves at `p` after `f` has taken `v_p f`, plus one: the
order of `g ^ k` is `orderOf g / gcd (orderOf g) k`, so `k` may absorb at most
`v_p (orderOf g) - v_p f` powers of `p`; the first forbidden exponent is that room plus one. -/
@[to_additive
/-- **When a number divides the additive order of a multiple.** Let `g` have finite additive order
and let `f` divide that order. Then `f` divides the additive order of `k • g` exactly when, for
every prime `p` of `f`, the exponent `k` is not divisible by
`p ^ (v_p (addOrderOf g) - v_p f + 1)`. -/]
theorem dvd_orderOf_pow_iff {g : G} (hg : IsOfFinOrder g) {f : ℕ}
    (hf : f ∣ orderOf g) (k : ℕ) :
    f ∣ orderOf (g ^ k) ↔
      ∀ p ∈ f.primeFactors, ¬p ^ ((orderOf g).factorization p - f.factorization p + 1) ∣ k := by
  have h0 : orderOf g ≠ 0 := hg.orderOf_pos.ne'
  rw [hg.orderOf_pow, Nat.dvd_div_iff_mul_dvd (Nat.gcd_dvd_left _ k), mul_comm,
    Nat.mul_dvd_iff_forall_not_pow_dvd h0 hf (Nat.gcd_dvd_left _ k)]
  refine forall₂_congr fun p hp => not_congr ?_
  rw [Nat.dvd_gcd_iff, and_iff_right (Nat.pow_factorization_sub_factorization_add_one_dvd hf hp)]

end IsOfFinOrder

namespace TauCeti



end TauCeti

end
end

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

/-- Reindexing the elements of a cyclic group of order `h` by `ZMod h`, through a generator: the
elements of order divisible by `f` correspond to the residues avoiding a prime power at each prime
of `f`. -/
@[to_additive]
private theorem IsCyclic.card_filter_dvd_orderOf_eq_card_zmod [_root_.NeZero (_root_.Fintype.card α)]
    (hf : f ∣ _root_.Fintype.card α) :
    #{τ : α | f ∣ _root_.orderOf τ}
      = #{x : _root_.ZMod (_root_.Fintype.card α) | ∀ p ∈ f.primeFactors,
          ¬p ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) ∣ x.val} := by
  obtain ⟨g, hgen⟩ := _root_.IsCyclic.exists_generator (α := α)
  have hg : _root_.orderOf g = _root_.Fintype.card α := by
    rw [_root_.orderOf_eq_card_of_forall_mem_zpowers hgen, _root_.Nat.card_eq_fintype_card]
  have hcrit : ∀ k : ℕ, f ∣ _root_.orderOf (g ^ k) ↔ ∀ p ∈ f.primeFactors,
      ¬p ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) ∣ k := by
    intro k
    have h := (_root_.isOfFinOrder_of_finite g).dvd_orderOf_pow_iff (hg ▸ hf) k
    rwa [hg] at h
  refine (_root_.Finset.card_bij (fun x _ => g ^ x.val) ?_ ?_ ?_).symm
  · intro x hx
    simp only [_root_.Finset.mem_filter, _root_.Finset.mem_univ, _root_.true_and] at hx ⊢
    exact (hcrit x.val).mpr hx
  · intro x _ y _ hxy
    have hlt : ∀ z : _root_.ZMod (_root_.Fintype.card α), z.val ∈ _root_.Set.Iio (_root_.orderOf g) := fun z => by
      rw [hg]; exact z.val_lt
    have : x.val = y.val := _root_.pow_injOn_Iio_orderOf (hlt x) (hlt y) hxy
    rw [← _root_.ZMod.natCast_zmod_val x, ← _root_.ZMod.natCast_zmod_val y, this]
  · intro τ hτ
    simp only [_root_.Finset.mem_filter, _root_.Finset.mem_univ, _root_.true_and] at hτ
    obtain ⟨k, hk⟩ := (_root_.Submonoid.mem_powers_iff τ g).mp
      ((_root_.isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr (hgen τ))
    refine ⟨(k : _root_.ZMod (_root_.Fintype.card α)), ?_, ?_⟩
    · simp only [_root_.Finset.mem_filter, _root_.Finset.mem_univ, _root_.true_and]
      refine (hcrit _).mp ?_
      rwa [_root_.ZMod.val_natCast, ← hg, _root_.pow_mod_orderOf, hk]
    · rw [_root_.ZMod.val_natCast, ← hg, _root_.pow_mod_orderOf, hk]

/-- **The number of elements of a cyclic group whose order is a multiple of `f`.** For `f`
dividing the order `h` of a cyclic group, the elements of order divisible by `f` number
`h * ∏ p ∣ f, (1 - p ^ -(v_p h - v_p f + 1))`, stated here cleared of denominators.

At `f = h` every exponent is `1` and this is Euler's product formula
`Nat.totient_mul_prod_primeFactors`, the elements of order divisible by `h` being the `φ h`
generators. -/

theorem solution (hf : f ∣ _root_.Fintype.card α) :
    #{τ : α | f ∣ _root_.orderOf τ} *
        ∏ p ∈ f.primeFactors,
          p ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1)
      = _root_.Fintype.card α *
        ∏ p ∈ f.primeFactors,
          (p ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) - 1) := by
  -- The three steps are: reindex the group by `ZMod h` through a generator (`hstep1`); reduce
  -- the resulting condition modulo the product of the prime powers it involves (`hstep2`); and
  -- split that product by the Chinese remainder theorem (`hstep3`).
  have : _root_.NeZero (_root_.Fintype.card α) := ⟨_root_.Fintype.card_ne_zero⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ,
      ∀ p, e p = (_root_.Fintype.card α).factorization p - f.factorization p + 1 := ⟨_, fun _ => _root_.rfl⟩
  -- the prime powers `p ^ e p`, indexed by the primes of `f`, are pairwise coprime and their
  -- product divides the order
  set a : ↥f.primeFactors → ℕ := fun i => (i : ℕ) ^ e i with ha
  have hprime : ∀ i : ↥f.primeFactors, (i : ℕ).Prime := fun i => _root_.Nat.prime_of_mem_primeFactors i.2
  have hane : ∀ i, _root_.NeZero (a i) := fun i => ⟨_root_.pow_ne_zero _ (hprime i).ne_zero⟩
  have : _root_.NeZero (∏ i, a i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (hane i).ne⟩
  have hcop : _root_.Pairwise (_root_.Nat.Coprime on a) := fun i j hij =>
    _root_.Nat.Coprime.pow _ _ ((_root_.Nat.coprime_primes (hprime i) (hprime j)).mpr
      fun h => hij (_root_.Subtype.ext h))
  have hprod : ∏ i, a i = ∏ p ∈ f.primeFactors, p ^ e p := by
    simp only [ha]
    exact _root_.Finset.prod_coe_sort f.primeFactors fun p => p ^ e p
  have hdvd : (∏ i, a i) ∣ _root_.Fintype.card α := by
    rw [hprod, _root_.Finset.prod_congr _root_.rfl fun p _ => by rw [he p]]
    exact _root_.Nat.prod_pow_factorization_sub_factorization_add_one_dvd hf
  have hmem : ∀ p (hp : p ∈ f.primeFactors), p ^ e p ∣ ∏ i, a i := fun p hp =>
    _root_.Finset.dvd_prod_of_mem a (_root_.Finset.mem_univ (⟨p, hp⟩ : ↥f.primeFactors))
  -- reducing a residue modulo a multiple of `p ^ e p` does not change divisibility by `p ^ e p`
  have hstep2 :
      (∏ i, a i) * #{x : _root_.ZMod (_root_.Fintype.card α) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val}
        = _root_.Fintype.card α * #{y : _root_.ZMod (∏ i, a i) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val} := by
    have key := _root_.ZMod.mul_card_filter_natCast_val (m := ∏ i, a i) (n := _root_.Fintype.card α) hdvd
      (Q := fun y : _root_.ZMod (∏ i, a i) => ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val)
    rwa [_root_.Finset.filter_congr (q := fun x : _root_.ZMod (_root_.Fintype.card α) =>
      ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val) fun x _ =>
      _root_.forall₂_congr fun p hp => _root_.not_congr (by
        rw [_root_.ZMod.val_natCast, _root_.Nat.dvd_mod_iff (hmem p hp)])] at key
  have hstep3 : #{y : _root_.ZMod (∏ i, a i) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val}
      = ∏ p ∈ f.primeFactors, (p ^ e p - 1) := by
    have key := _root_.ZMod.card_filter_forall_natCast_val a hcop
      (Q := fun i (z : _root_.ZMod (a i)) => ¬a i ∣ z.val)
    rw [_root_.Finset.filter_congr (q := fun y : _root_.ZMod (∏ i, a i) =>
      ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val) fun y _ => by
        rw [_root_.Subtype.forall]
        exact _root_.forall₂_congr fun p hp => _root_.not_congr (by
          rw [_root_.ZMod.val_natCast, _root_.Nat.dvd_mod_iff _root_.dvd_rfl])] at key
    rw [key, _root_.Finset.prod_congr _root_.rfl fun i _ => _root_.ZMod.card_filter_not_self_dvd_val,
      _root_.Finset.prod_coe_sort f.primeFactors fun p => p ^ e p - 1]
  have hstep1 : #{τ : α | f ∣ _root_.orderOf τ}
      = #{x : _root_.ZMod (_root_.Fintype.card α) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val} := by
    have key := _root_.IsCyclic.card_filter_dvd_orderOf_eq_card_zmod (α := α) (f := f) hf
    rwa [_root_.Finset.filter_congr (q := fun x : _root_.ZMod (_root_.Fintype.card α) =>
      ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val) fun x _ =>
      _root_.forall₂_congr fun p _ => _root_.not_congr (by rw [he p])] at key
  simp only [← he]
  calc #{τ : α | f ∣ _root_.orderOf τ} * ∏ p ∈ f.primeFactors, p ^ e p
      = (∏ i, a i) * #{x : _root_.ZMod (_root_.Fintype.card α) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ x.val} := by
        rw [hprod, hstep1]; ring
    _ = _root_.Fintype.card α * #{y : _root_.ZMod (∏ i, a i) | ∀ p ∈ f.primeFactors, ¬p ^ e p ∣ y.val} := hstep2
    _ = _root_.Fintype.card α * ∏ p ∈ f.primeFactors, (p ^ e p - 1) := by rw [hstep3]





end IsCyclic

end
end
