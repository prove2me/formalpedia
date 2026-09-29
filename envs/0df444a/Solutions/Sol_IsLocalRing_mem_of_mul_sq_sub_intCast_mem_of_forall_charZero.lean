-- Prove2me | solution 1 for IsLocalRing.mem_of_mul_sq_sub_intCast_mem_of_forall_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8b006deb-4e9d-53e7-95a6-dc632bf096fb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero

set_option autoImplicit false

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] (r : R) (d : ℤ)
    (hmax : r ∈ IsLocalRing.maximalIdeal R)
    (hquad : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → r * (r ^ 2 - (d : R)) ∈ 𝔭)
    (hzero : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → CharZero (R ⧸ 𝔭) → r ∈ 𝔭)
    (𝔭 : Ideal R) (h𝔭 : 𝔭.IsPrime) : r ∈ 𝔭 := by
  classical
  rcases h𝔭.mem_or_mem (hquad 𝔭 h𝔭) with h | h
  · exact h

  have hle : 𝔭 ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal h𝔭.ne_top
  have hdm : (d : R) ∈ IsLocalRing.maximalIdeal R := by
    have h1 : r ^ 2 - (d : R) ∈ IsLocalRing.maximalIdeal R := hle h
    have h2 : r ^ 2 ∈ IsLocalRing.maximalIdeal R := Ideal.pow_mem_of_mem _ hmax 2 (by norm_num)
    have h3 := Ideal.sub_mem _ h2 h1
    simpa using h3
  haveI : 𝔭.IsPrime := h𝔭
  obtain ⟨p, hp⟩ := CharP.exists (R ⧸ 𝔭)
  rcases CharP.char_is_prime_or_zero (R ⧸ 𝔭) p with hpp | hp0
  ·
    have hpmem : (p : R) ∈ 𝔭 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero (R ⧸ 𝔭) p
    have hpd : (p : ℤ) ∣ d := by
      by_contra hnd
      have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hpp).irreducible
      have hcop : IsCoprime (p : ℤ) d := (Irreducible.coprime_iff_not_dvd hirr).mpr hnd
      obtain ⟨u, v, huv⟩ := hcop
      have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have : ((u * p + v * d : ℤ) : R) ∈ IsLocalRing.maximalIdeal R := by
          push_cast
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hle hpmem)) (Ideal.mul_mem_left _ _ hdm)
        rw [huv, Int.cast_one] at this
        exact this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h1
    obtain ⟨e, he⟩ := hpd
    have hdp : (d : R) ∈ 𝔭 := by
      rw [he]; push_cast
      exact Ideal.mul_mem_right _ _ hpmem
    have hr2 : r ^ 2 ∈ 𝔭 := by
      have := Ideal.add_mem _ h hdp
      simpa using this
    exact h𝔭.mem_of_pow_mem 2 hr2
  ·
    subst hp0
    haveI : CharZero (R ⧸ 𝔭) := CharP.charP_to_charZero (R ⧸ 𝔭)
    exact hzero 𝔭 h𝔭 inferInstance

end S_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero
end P2MW
export P2MW.S_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero (solution)
