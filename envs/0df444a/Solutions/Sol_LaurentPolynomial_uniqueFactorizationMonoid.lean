-- Prove2me | solution 1 for LaurentPolynomial.uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/55e6b366-4944-556f-9e0c-703c55cddf21

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentPolynomial_uniqueFactorizationMonoid
set_option autoImplicit false
set_option maxHeartbeats 3200000
universe u v

open scoped Polynomial
open LaurentPolynomial

namespace LaurentUFD

theorem uniqueFactorizationMonoid_of_isLocalization
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] : UniqueFactorizationMonoid S := by
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun J hJ hJp => ?_
  haveI := hJp

  set I : Ideal R := J.under R with hI
  haveI hIp : I.IsPrime := Ideal.IsPrime.under R J
  have hI0 : I ≠ ⊥ := by
    intro h0
    apply hJ
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M s
    have hr : algebraMap R S r ∈ J := by
      have := J.mul_mem_left (algebraMap R S m) hs
      rwa [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left] at this
    have hrI : r ∈ I := Ideal.mem_comap.mpr hr
    rw [h0, Ideal.mem_bot] at hrI
    rw [Submodule.mem_bot, hrI]
    exact IsLocalization.mk'_zero _

  obtain ⟨p, hpI, hp⟩ := (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp ‹_› I hI0 hIp)
  refine ⟨algebraMap R S p, Ideal.mem_comap.mp hpI, ?_⟩

  have hdisj : Disjoint (M : Set R) (Ideal.span {p} : Set R) := by
    rw [Set.disjoint_left]
    intro m hm hmp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hmp
    have hu : IsUnit (algebraMap R S (c * p)) := IsLocalization.map_units S ⟨c * p, hm⟩
    rw [map_mul] at hu
    exact hJp.ne_top (J.eq_top_of_isUnit_mem (Ideal.mem_comap.mp hpI) (isUnit_of_mul_isUnit_right hu))
  have hprime : (Ideal.map (algebraMap R S) (Ideal.span {p})).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S _ ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hdisj
  rw [Ideal.map_span, Set.image_singleton] at hprime
  have hp0 : algebraMap R S p ≠ 0 := fun h =>
    hp.ne_zero ((IsLocalization.injective S hM) (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hp0).mp hprime

theorem laurentPolynomial (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  uniqueFactorizationMonoid_of_isLocalization (Submonoid.powers (Polynomial.X : R[X]))
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero) R[T;T⁻¹]

end LaurentUFD

theorem solution (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  LaurentUFD.laurentPolynomial R

end S_LaurentPolynomial_uniqueFactorizationMonoid
end P2MW
export P2MW.S_LaurentPolynomial_uniqueFactorizationMonoid (solution)
