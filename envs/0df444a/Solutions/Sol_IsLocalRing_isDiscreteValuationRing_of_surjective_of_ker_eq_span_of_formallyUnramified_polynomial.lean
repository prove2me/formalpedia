-- Prove2me | solution 1 for IsLocalRing.isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/43448a1d-71de-59b7-a6ad-65ac4ba575a8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφu : φ.FormallyUnramified) (hφf : φ.EssFiniteType)
    (ht : φ Polynomial.X ∈ IsLocalRing.maximalIdeal S)
    {T : Type} [CommRing T] [IsDomain T]
    (π : S →+* T) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {φ (Polynomial.C ϖ)})
    (ht0 : π (φ Polynomial.X) ≠ 0) :
    ∃ _ : IsDiscreteValuationRing T, IsLocalRing.maximalIdeal T = Ideal.span {π (φ Polynomial.X)} := by
  classical

  letI algS : Algebra (Polynomial A) S := φ.toAlgebra
  haveI hfu : Algebra.FormallyUnramified (Polynomial A) S := hφu
  haveI hft : Algebra.EssFiniteType (Polynomial A) S := hφf
  have hφalg : algebraMap (Polynomial A) S = φ := rfl

  haveI : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing (Polynomial A) S
  haveI : IsNoetherianRing T := isNoetherianRing_of_surjective S T π hπ
  haveI : IsLocalRing T := IsLocalRing.of_surjective' π hπ

  have hϖS : φ (C ϖ) ∈ maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have htop : RingHom.ker π = ⊤ := by
      rw [hker, Ideal.span_singleton_eq_top]
      exact hu
    have h1 : (1 : S) ∈ RingHom.ker π := htop ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1

  set P : Ideal (Polynomial A) := (maximalIdeal S).comap φ with hPdef
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime φ (maximalIdeal S)
  have hCP : C ϖ ∈ P := hϖS
  have hXP : (X : Polynomial A) ∈ P := ht
  have hPle : P ≤ Ideal.span {C ϖ, (X : Polynomial A)} := by
    intro f hf
    have hsplit : (X : Polynomial A) * f.divX + C (f.coeff 0) = f := X_mul_divX_add f
    have hXf : (X : Polynomial A) * f.divX ∈ P := Ideal.mul_mem_right _ _ hXP
    have hC0 : C (f.coeff 0) ∈ P := by
      have : C (f.coeff 0) = f - X * f.divX := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hsplit
      rw [this]
      exact Ideal.sub_mem _ hf hXf

    have hc0 : f.coeff 0 ∈ maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' : IsUnit (φ (C (f.coeff 0))) := (hu.map C).map φ
      have hm : φ (C (f.coeff 0)) ∈ maximalIdeal S := hC0
      exact (IsLocalRing.mem_maximalIdeal _).mp hm hu'
    rw [hϖ, Ideal.mem_span_singleton'] at hc0
    obtain ⟨a, ha⟩ := hc0
    rw [← hsplit, ← ha, map_mul]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hPge : Ideal.span {C ϖ, (X : Polynomial A)} ≤ P := by
    rw [Ideal.span_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hCP
    · exact hXP
  have hPeq : P = Ideal.span {C ϖ, (X : Polynomial A)} := le_antisymm hPle hPge

  let R := Localization.AtPrime P
  have hunits : ∀ y : P.primeCompl, IsUnit (φ y) := by
    intro y
    have hy : (y : Polynomial A) ∉ P := y.2
    by_contra hnu
    exact hy ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  let ψ : R →+* S := IsLocalization.lift (M := P.primeCompl) (g := φ) hunits
  have hψcomp : ψ.comp (algebraMap (Polynomial A) R) = φ := IsLocalization.lift_comp hunits
  letI algRS : Algebra R S := ψ.toAlgebra
  have hψalg : algebraMap R S = ψ := rfl
  haveI : IsScalarTower (Polynomial A) R S :=
    IsScalarTower.of_algebraMap_eq' (by rw [hψalg, hφalg, hψcomp])
  haveI : IsLocalHom (algebraMap R S) := by
    have hle : maximalIdeal R ≤ (maximalIdeal S).comap (algebraMap R S) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap,
        hψalg, hψcomp]
    exact ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 3 0).mp hle
  haveI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_comp (Polynomial A) R S
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.of_restrictScalars (Polynomial A) R S

  have hmapS : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hmS : maximalIdeal S = Ideal.span {φ (C ϖ), φ X} := by
    rw [← hmapS, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hψalg, hψcomp, hPeq,
      Ideal.map_span, Set.image_pair]

  have hmT : maximalIdeal T = Ideal.span {π (φ X)} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective π hπ, hmS, Ideal.map_span, Set.image_pair]
    have h0 : π (φ (C ϖ)) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.span_insert_zero]

  have hnf : ¬ IsField T := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmT, Ideal.span_singleton_eq_bot]
    exact ht0
  have hprinc : (maximalIdeal T).IsPrincipal := ⟨⟨π (φ X), by rw [hmT]⟩⟩
  have hdvr : IsDiscreteValuationRing T := ((IsDiscreteValuationRing.TFAE T hnf).out 0 4).mpr hprinc
  exact ⟨hdvr, hmT⟩

end S_IsLocalRing_isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial
end P2MW
export P2MW.S_IsLocalRing_isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial (solution)
