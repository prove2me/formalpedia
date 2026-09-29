-- Prove2me | solution 1 for IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0d543fde-8951-59b2-ba10-9a5def91ac91

import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two

set_option autoImplicit false

open IsLocalRing

namespace AB2Prin

theorem isPrincipal_of_isPrime_of_height_eq_one_of_ufd {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (P : Ideal A) (hP : P.IsPrime) (hP1 : P.height = 1) :
    Submodule.IsPrincipal P := by
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hP1
    exact zero_ne_one hP1
  obtain ⟨p, hpP, hp⟩ := hP.exists_mem_prime_of_ne_bot hPbot
  have hp0 : p ≠ 0 := hp.ne_zero
  have hQ : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp0).mpr hp
  have hQP : Ideal.span {p} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hpP
  suffices h : Ideal.span {p} = P from h ▸ ⟨⟨p, rfl⟩⟩
  by_contra hne
  have hlt : Ideal.span {p} < P := lt_of_le_of_ne hQP hne
  haveI := hP
  have hle : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hP1]; exact_mod_cast le_rfl
  have hQlt : (Ideal.span {p}).height < ((1 : ℕ) : ℕ∞) := Ideal.height_le_iff.mp hle _ hQ hlt
  have hQ0 : (Ideal.span {p}).height = 0 := by
    rw [Nat.cast_one] at hQlt
    exact ENat.lt_one_iff_eq_zero.mp hQlt
  haveI := hQ
  have hmin : Ideal.span {p} ∈ minimalPrimes A := Ideal.height_eq_zero_iff.mp hQ0
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff, Ideal.span_singleton_eq_bot] at hmin
  exact hp0 hmin

end AB2Prin

open AB2Prin in
theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (P : Ideal R) (hP : P.IsPrime) (hP1 : P.height = 1) :
    Submodule.IsPrincipal P := by
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  haveI : UniqueFactorizationMonoid R :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim
  exact isPrincipal_of_isPrime_of_height_eq_one_of_ufd P hP hP1

end S_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
end P2MW
export P2MW.S_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two (solution)
