-- Prove2me | solution 1 for IsLocalRing.exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2139ab4f-bb3a-5efa-a86d-ca8e95daf70f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RED1c

theorem isUnit_of_forall_maximal_not_mem {L : Type*} [CommRing L] (x : L)
    (h : ∀ M : Ideal L, M.IsMaximal → x ∉ M) : IsUnit x := by
  by_contra hx
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro htop
    exact hx (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  exact h M hM (hle (Ideal.subset_span rfl))

theorem isUnit_algebraMap_of_map_maximalIdeal_eq_top
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    {L : Type} [CommRing L] [Algebra R L]
    (hgen : Ideal.map (algebraMap R L) (IsLocalRing.maximalIdeal R) = ⊤) {d : R} (hd : d ≠ 0) :
    IsUnit (algebraMap R L d) := by
  apply isUnit_of_forall_maximal_not_mem
  intro M hM hdM

  let P : Ideal R := M.comap (algebraMap R L)
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPne : P ≠ IsLocalRing.maximalIdeal R := by
    intro hP
    apply hM.ne_top
    rw [eq_top_iff, ← hgen, Ideal.map_le_iff_le_comap, ← hP]
  have hPbot : P = ⊥ := by
    by_contra hne
    exact hPne (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne))
  have : d ∈ P := hdM
  rw [hPbot, Ideal.mem_bot] at this
  exact hd this

theorem algebraMap_away_surjective {H : Type*} [CommRing H] {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away (1 - e) L] :
    Function.Surjective (algebraMap H L) := by
  intro w
  obtain ⟨⟨h, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (1 - e)) w

  have h1e : IsIdempotentElem (1 - e) := he.one_sub
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hs1 : algebraMap H L s = 1 := by
    have hu : IsUnit (algebraMap H L (1 - e)) := IsLocalization.Away.algebraMap_isUnit (1 - e)
    have hid : IsIdempotentElem (algebraMap H L (1 - e)) := h1e.map (algebraMap H L)
    have h11 : algebraMap H L (1 - e) = 1 := by
      obtain ⟨u, hu'⟩ := hu
      have := hid.eq
      rw [← hu'] at this ⊢
      have h2 : (u : L) * u * ↑u⁻¹ = u * ↑u⁻¹ := by rw [this]
      rw [mul_assoc, Units.mul_inv, mul_one] at h2
      exact h2
    rw [← hn, map_pow, h11, one_pow]
  refine ⟨h, ?_⟩
  show algebraMap H L h = IsLocalization.mk' L h s
  rw [IsLocalization.eq_mk'_iff_mul_eq, hs1, mul_one]

end RED1c

open RED1c in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (H : Type) [CommRing H] [Algebra R H] (e : H) (he : IsIdempotentElem e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e) := by
  intro d hd y
  set L := Localization.Away (1 - e)
  have hu : IsUnit (algebraMap R L d) := isUnit_algebraMap_of_map_maximalIdeal_eq_top hgen hd
  obtain ⟨u, hu'⟩ := hu

  obtain ⟨z, hz⟩ := algebraMap_away_surjective he L (↑u⁻¹ * algebraMap H L y)
  refine ⟨z, ?_⟩

  have hdz : algebraMap H L (d • z) = algebraMap H L y := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← hu', hz, ← mul_assoc, Units.mul_inv,
      one_mul]
  have hker : algebraMap H L (d • z - y) = 0 := by rw [map_sub, hdz, sub_self]
  obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (1 - e)) L _).mp hker
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm

  have h1e : IsIdempotentElem (1 - e) := he.one_sub
  have hkill : (1 - e) * (d • z - y) = 0 := by
    have hm0' : (1 - e) ^ n * (d • z - y) = 0 := hm0
    calc (1 - e) * (d • z - y) = (1 - e) * ((1 - e) ^ n * (d • z - y)) := by
          rw [← mul_assoc, ← pow_succ', h1e.pow_succ_eq]
      _ = 0 := by rw [hm0', mul_zero]
  have hfin : (d • z - y) * (1 - e) = 0 := by rw [mul_comm]; exact hkill
  rw [sub_mul, sub_eq_zero, Algebra.smul_def, mul_assoc] at hfin
  rw [Algebra.smul_def, ← mul_assoc]
  rw [← mul_assoc] at hfin
  exact hfin

end S_IsLocalRing_exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top
end P2MW
export P2MW.S_IsLocalRing_exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top (solution)
