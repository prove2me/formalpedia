-- Prove2me | solution 1 for IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c224f5c5-c892-5664-9990-a03b077ca6c2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff

set_option autoImplicit false

universe u

theorem solution
    {A₀ : Type u} [CommRing A₀] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra A₀ R]
    (T : Subalgebra A₀ R) [IsNoetherianRing ↥T] :
    ∃ S : Subalgebra A₀ R,
      (S : Set R) = {x : R | ∃ t ∈ T, ∃ u ∈ T, u ∉ IsLocalRing.maximalIdeal R ∧ x * u = t} ∧
      IsNoetherianRing ↥S ∧ IsLocalRing ↥S ∧ ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R) := by
  classical

  let 𝔭 : Ideal ↥T := (IsLocalRing.maximalIdeal R).comap T.val.toRingHom
  haveI h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hunitR : ∀ u : ↥T, u ∉ 𝔭 ↔ IsUnit (u : R) := by
    intro u
    change (u : R) ∉ IsLocalRing.maximalIdeal R ↔ IsUnit (u : R)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hM : ∀ y : 𝔭.primeCompl, IsUnit (T.val.toRingHom (y : ↥T)) := fun y =>
    (hunitR y.1).mp (Ideal.mem_primeCompl_iff.mp y.2)
  let ψ : Localization.AtPrime 𝔭 →+* R := IsLocalization.lift (M := 𝔭.primeCompl) hM
  have hψT : ∀ t : ↥T, ψ (algebraMap (↥T) _ t) = (t : R) := fun t => IsLocalization.lift_eq hM t
  have hψmk : ∀ (t : ↥T) (u : 𝔭.primeCompl), ψ (IsLocalization.mk' _ t u) * (u : R) = (t : R) := by
    intro t u
    have := IsLocalization.lift_mk'_spec (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) hM t u

    rw [← hψT t, ← IsLocalization.mk'_spec (Localization.AtPrime 𝔭) t u, map_mul, hψT]
  let ψₐ : Localization.AtPrime 𝔭 →ₐ[A₀] R :=
    { toRingHom := ψ
      commutes' := fun a => by
        change ψ (algebraMap A₀ (Localization.AtPrime 𝔭) a) = algebraMap A₀ R a
        rw [IsScalarTower.algebraMap_apply A₀ (↥T) (Localization.AtPrime 𝔭), hψT]
        rfl }
  have hψinj : Function.Injective ψₐ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl x
    change ψ (IsLocalization.mk' _ t u) = 0 at hx
    have h := hψmk t u
    rw [hx, zero_mul] at h
    have ht : t = 0 := Subtype.ext (by rw [← h]; rfl)
    change IsLocalization.mk' (Localization.AtPrime 𝔭) t u = 0
    rw [ht, IsLocalization.mk'_zero]
  let e : Localization.AtPrime 𝔭 ≃ₐ[A₀] ↥ψₐ.range := AlgEquiv.ofInjective ψₐ hψinj
  have he : ∀ y, ((e y : ↥ψₐ.range) : R) = ψ y := fun y => rfl
  refine ⟨ψₐ.range, ?_, ?_, ?_, ?_⟩
  ·
    ext x
    rw [AlgHom.coe_range, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
      refine ⟨(t : R), t.2, ((u : ↥T) : R), (u : ↥T).2, ?_, hψmk t u⟩
      exact fun hu => (Ideal.mem_primeCompl_iff.mp u.2) hu
    · rintro ⟨t, ht, u, hu, hu𝔪, hx⟩
      have hu' : (⟨u, hu⟩ : ↥T) ∈ 𝔭.primeCompl := Ideal.mem_primeCompl_iff.mpr hu𝔪
      refine ⟨IsLocalization.mk' _ (⟨t, ht⟩ : ↥T) ⟨⟨u, hu⟩, hu'⟩, ?_⟩
      have huR : IsUnit u := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu𝔪; exact hu𝔪
      apply huR.mul_left_inj.mp
      change ψ _ * u = x * u
      rw [hx]
      exact hψmk ⟨t, ht⟩ ⟨⟨u, hu⟩, hu'⟩
  ·
    exact isNoetherianRing_of_ringEquiv (Localization.AtPrime 𝔭) e.toRingEquiv
  ·
    exact IsLocalRing.of_surjective' e.toRingEquiv.toRingHom e.surjective
  ·
    intro x
    constructor
    · intro hx; exact hx.map ψₐ.range.val
    · intro hx
      obtain ⟨y, rfl⟩ := e.surjective x
      obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
      rw [he] at hx

      have huR : IsUnit (((u : ↥T)) : R) := hM u
      have htR : IsUnit ((t : ↥T) : R) := by
        rw [← hψmk t u]; exact hx.mul huR
      have ht : (t : ↥T) ∈ 𝔭.primeCompl := Ideal.mem_primeCompl_iff.mpr ((hunitR t).mpr htR)
      have hunit : IsUnit (IsLocalization.mk' (Localization.AtPrime 𝔭) t u) :=
        IsUnit.of_mul_eq_one (b := IsLocalization.mk' (Localization.AtPrime 𝔭) (u : ↥T) ⟨t, ht⟩)
          (by rw [← IsLocalization.mk'_mul, mul_comm]; exact IsLocalization.mk'_self _ _)
      exact hunit.map e

end S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
end P2MW
export P2MW.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff (solution)
