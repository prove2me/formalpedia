-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.encard_setOf_under_eq_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:45.893107+00:00
-- url     : https://prove2.me/submissions/d4e31fc9-a3f8-406e-a9fe-12e9dec2c213

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification indices in finite flat towers

This file records consequences of the fundamental identity for ramification and inertia in a finite
flat extension of domains. The number of primes above a prime and each prime's contribution are at
most the rank of the extension. Ramification also cancels in a tower when the absolute ramification
index at the top equals the absolute ramification index at the intermediate prime: multiplicativity
then forces the relative ramification index to be one.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_le_finrank`: the number of primes above a prime is
  at most the rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_of_eq_ramificationIdx`: equal absolute
  ramification indices at two levels of a tower force relative ramification index one.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime, then the intermediate prime is unramified in
  the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
* `TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`: unramifiedness over the
  base descends from an integral extension to the subring below it, for `S` integral and
  torsion-free over the Dedekind domain `R`, with `R` and `S` both essentially of finite type over
  the base `A` and `A ≤ R ≤ S` a scalar tower. The base ring and the ideal are arbitrary.
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]

/-- **There are at most `Module.finrank R S` primes above a prime.** Every ramification index and
inertia degree in the fundamental identity is positive, so every prime above `p` contributes at
least one to the rank. -/
theorem ncard_primesOver_le_finrank (p : Ideal R) [p.IsPrime] :
    (p.primesOver S).ncard ≤ finrank R S := by
  have : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones, ← Ideal.sum_ramification_inertia_eq_finrank p S]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have : q.1.IsPrime := q.2.1
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (q.1.ramificationIdx_pos R).ne' (q.1.inertiaDeg_pos R).ne')





end Bounds

section Tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Module.Finite R S] [Module.Flat S T]









end Tower

section Descent

variable {A R S : Type*} [CommRing A] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [Algebra.IsIntegral R S]
  [Module.IsTorsionFree R S] [Algebra.EssFiniteType A R] [Algebra.EssFiniteType A S]

-- Source. Recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c.



end Descent

end TauCeti.RamificationInertia

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
# The residue degree of a height-one prime over `ℚ`

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file names the two
objects that description involves and records their elementary theory.

## Main definitions

* `TauCeti.rationalPrimeBelow 𝔭` is the rational prime below a height-one prime `𝔭` of `𝓞 K`,
  namely the absolute norm of `𝔭 ∩ ℤ`.
* `TauCeti.higherDegreePrimes K` is the set of height-one primes of `𝓞 K` whose residue degree
  over `ℚ` exceeds `1`.
* `TauCeti.primesDividing K n hn` is the finite set of height-one primes of `𝓞 K` whose rational
  prime below divides a nonzero integer `n`.

## Main results

* `TauCeti.absNorm_eq_rationalPrimeBelow_pow`: the absolute norm of `𝔭` is the rational prime
  below it raised to the residue degree.
* `TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm`: a height-one prime has residue degree
  above one exactly when its absolute norm is not a prime number.
* `TauCeti.rationalPrimeBelow_pow_le_absNorm`: the norm of `𝔭` is at least the rational prime
  below it raised to any power at most the residue degree.
* `TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg`: residue degree above one over an
  intermediate number field forces residue degree above one over `ℚ`.
* `TauCeti.card_filter_rationalPrimeBelow_le_finrank`: at most `[K : ℚ]` height-one primes have
  a given rational prime below them.
* `IsDedekindDomain.HeightOneSpectrum.encard_setOf_under_eq_le_finrank`: at most `[E : K]`
  height-one primes of `E` contract to a given height-one prime of an intermediate number field
  `K`.
* `IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`: the absolute
  norm of `𝔭` divides `p ^ [K : ℚ]`, so the residue degree is at most the degree of the field.
* `TauCeti.asIdeal_eq_span_singleton_of_absNorm_eq_pow_finrank`: a prime of full residue degree
  is inert, that is, generated by the rational prime below it.
* `IsDedekindDomain.HeightOneSpectrum.intCast_mem_asIdeal_iff`: an integer belongs to a
  height-one prime exactly when the rational prime below it divides that integer.
* `TauCeti.mem_primesDividing`: the defining condition for membership in `primesDividing`.

## Implementation notes

`rationalPrimeBelow` is named rather than spelled out as `Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)`
because the estimates downstream fibre the primes over it: keeping it a single head symbol is what
makes the fibrewise rewriting elaborate, and it is the object `Chebotarev` will name when it
compares a prime of `K` with the rational prime under it.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {K : Type*} [Field K] [NumberField K]





/-! ### The rational prime below a height-one prime -/

















/-! ### Fibring the primes over the rational primes below them -/



/-- At most `[E : K]` height-one primes of `E` contract to a given height-one prime of `K`. -/
theorem solution
    {E : Type*} [_root_.Field E] [_root_.NumberField E] [_root_.Algebra K E]
    (p : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E) | P.under (𝓞 K) = p}.encard ≤ _root_.Module.finrank K E := by
  let hdiv : ∀ P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      P.under (𝓞 K) = p ↔
        P.asIdeal ∣ _root_.Ideal.map (_root_.Algebra.algebraMap (𝓞 K) (𝓞 E)) p.asIdeal := fun P ↦ by
    rw [← _root_.Ideal.liesOver_iff_dvd_map P.isPrime.ne_top]
    exact ⟨fun h ↦ ⟨(_root_.congrArg _root_.IsDedekindDomain.HeightOneSpectrum.asIdeal h).symm⟩,
      fun h ↦ _root_.IsDedekindDomain.HeightOneSpectrum.ext h.over.symm⟩
  let e : {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E) // P.under (𝓞 K) = p} ≃
      p.asIdeal.primesOver (𝓞 E) :=
    (_root_.Equiv.subtypeEquivRight hdiv).trans
      (_root_.IsDedekindDomain.HeightOneSpectrum.equivPrimesOver (𝓞 E) p.ne_bot)
  have hfin : (p.asIdeal.primesOver (𝓞 E)).Finite :=
    _root_.Algebra.QuasiFinite.finite_primesOver p.asIdeal
  calc
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 E) | P.under (𝓞 K) = p}.encard =
        (p.asIdeal.primesOver (𝓞 E)).encard := _root_.Set.encard_congr e
    _ = (p.asIdeal.primesOver (𝓞 E)).ncard := hfin.cast_ncard_eq.symm
    _ ≤ _root_.Module.finrank K E := by
      exact ENat.natCast_le_natCast.mpr <| by
        simpa only [_root_.IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E] using
          _root_.TauCeti.RamificationInertia.ncard_primesOver_le_finrank (S := 𝓞 E) p.asIdeal

/-! ### Inert primes -/







/-! ### The primes dividing an integer -/









end TauCeti

end
end
