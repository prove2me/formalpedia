-- Prove2me | solution 1 for IsDiscreteValuationRing.mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/29bbe931-2e54-59b3-a254-9ab1e4f6931a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem

set_option autoImplicit false

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (a v : 𝒪) (k M : ℕ)
    (hk : a ∉ IsLocalRing.maximalIdeal 𝒪 ^ (k + 1))
    (h : a * v ∈ IsLocalRing.maximalIdeal 𝒪 ^ M) :
    v ∈ IsLocalRing.maximalIdeal 𝒪 ^ (M - k) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hk h ⊢

  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero _)
  by_cases hv0 : v = 0
  · rw [hv0]; exact dvd_zero _

  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hϖ

  have hik : i ≤ k := by
    by_contra hlt
    exact hk (dvd_mul_of_dvd_right (pow_dvd_pow ϖ (by omega)) _)

  have hM : M ≤ i + j := by
    have h' : ϖ ^ M ∣ ϖ ^ (i + j) := by
      rw [show (u : 𝒪) * ϖ ^ i * ((u' : 𝒪) * ϖ ^ j) = ((u * u' : 𝒪ˣ) : 𝒪) * ϖ ^ (i + j) by
        rw [Units.val_mul, pow_add]; ring] at h
      exact (Units.isUnit (u * u')).dvd_mul_left.mp h
    exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h'
  exact dvd_mul_of_dvd_right (pow_dvd_pow ϖ (by omega)) _

end S_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
end P2MW
export P2MW.S_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem (solution)
