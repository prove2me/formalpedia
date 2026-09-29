-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_dvr_extension_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b838ec78-f8e4-5b54-882f-06eb751d978e

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_dvr_extension_pow_eq

set_option autoImplicit false

universe u

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (n : ℕ) (hn : IsUnit ((n : ℕ) : R₀)) (hn0 : 0 < n) (π : R₀) (hπ : π ≠ 0) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K')
      (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' K') (_ : IsFractionRing A' K') (f : R₀ →+* A'),
      (algebraMap A' K').comp f = (algebraMap K K').comp (algebraMap R₀ K) ∧
      (∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K)) ∧
      ∃ ϖ : A', (algebraMap A' K' ϖ) ^ n = algebraMap K K' (algebraMap R₀ K π) := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  have hπK0 : algebraMap R₀ K π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ
  have hnK : (n : K) ≠ 0 := by
    have := (hn.map (algebraMap R₀ K)).ne_zero
    rwa [map_natCast] at this
  have hgsep : (Polynomial.X ^ n - Polynomial.C (algebraMap R₀ K π) : Polynomial K).Separable :=
    Polynomial.separable_X_pow_sub_C _ hnK hπK0

  let K' : Type u := (Polynomial.X ^ n - Polynomial.C (algebraMap R₀ K π) : Polynomial K).SplittingField
  haveI : IsGalois K K' :=
    IsGalois.of_separable_splitting_field (p := (Polynomial.X ^ n - Polynomial.C (algebraMap R₀ K π) : Polynomial K)) hgsep

  let B := integralClosure R₀ K'
  haveI hBded : IsDedekindDomain B := integralClosure.isDedekindDomain R₀ K K'
  haveI hBfrac : IsFractionRing B K' := IsIntegralClosure.isFractionRing_of_finite_extension R₀ K K' B
  haveI hBint : Algebra.IsIntegral R₀ B := IsIntegralClosure.isIntegral_algebra R₀ K'
  have hBinj : Function.Injective (algebraMap R₀ B) := by
    intro x y hxy
    have := congrArg (algebraMap B K') hxy
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R₀ K K', IsScalarTower.algebraMap_apply R₀ K K'] at this
    exact hinj ((algebraMap K K').injective this)

  obtain ⟨P, hPmax, hPcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B)
    (IsLocalRing.maximalIdeal R₀) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hBinj]; exact bot_le)
  haveI := hPmax
  have hP0 : P ≠ ⊥ := by
    intro hP
    have h1 : Ideal.comap (algebraMap R₀ B) ⊥ = ⊥ := by
      rw [Ideal.comap_bot_of_injective _ hBinj]
    rw [hP, h1] at hPcomap
    exact IsDiscreteValuationRing.not_isField R₀ (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hPcomap.symm)

  haveI hA'dvr : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 (Localization.AtPrime P)
  have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap B K' y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro h0
    apply y.2
    have : (y : B) = 0 := (IsFractionRing.injective B K') (by rw [h0, map_zero])
    rw [this]
    exact P.zero_mem
  letI algA'K' : Algebra (Localization.AtPrime P) K' := (IsLocalization.lift (M := P.primeCompl) (S := (Localization.AtPrime P)) hunits).toAlgebra
  have halg : ∀ b : B, algebraMap (Localization.AtPrime P) K' (algebraMap B (Localization.AtPrime P) b) = algebraMap B K' b :=
    fun b => IsLocalization.lift_eq hunits b
  haveI : IsScalarTower B (Localization.AtPrime P) K' := IsScalarTower.of_algebraMap_eq (fun b => (halg b).symm)
  haveI hA'frac : IsFractionRing (Localization.AtPrime P) K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl (Localization.AtPrime P) K'
  refine ⟨K', inferInstance, inferInstance, (Localization.AtPrime P), inferInstance, inferInstance, hA'dvr, algA'K', hA'frac,
    (algebraMap B (Localization.AtPrime P)).comp (algebraMap R₀ B), ?_, ?_, ?_⟩
  ·
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, halg, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R₀ K K']
  ·
    rintro x ⟨y, hy⟩
    rcases ValuationRing.isInteger_or_isInteger R₀ x with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, hr⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hru : IsUnit r
      · obtain ⟨u, rfl⟩ := hru
        refine ⟨((u⁻¹ : R₀ˣ) : R₀), ?_⟩
        have hmul : algebraMap R₀ K (u : R₀) * algebraMap R₀ K ((u⁻¹ : R₀ˣ) : R₀) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [eq_inv_of_mul_eq_one_right hmul, hr, inv_inv]
      · exfalso
        have hrm : r ∈ IsLocalRing.maximalIdeal R₀ := (IsLocalRing.mem_maximalIdeal _).mpr hru
        rw [← hPcomap, Ideal.mem_comap] at hrm
        have hmax : algebraMap B (Localization.AtPrime P) (algebraMap R₀ B r) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr hrm
        apply (IsLocalRing.mem_maximalIdeal _).mp hmax
        have hK' : algebraMap (Localization.AtPrime P) K' (y * algebraMap B (Localization.AtPrime P) (algebraMap R₀ B r)) = 1 := by
          rw [map_mul, hy, halg, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₀ K K',
            hr, ← map_mul, mul_inv_cancel₀ hx0, map_one]
        have h1 : y * algebraMap B (Localization.AtPrime P) (algebraMap R₀ B r) = 1 :=
          (IsFractionRing.injective (Localization.AtPrime P) K') (by rw [hK', map_one])
        exact isUnit_iff_exists_inv.mpr ⟨y, by rw [mul_comm]; exact h1⟩
  ·
    have hsplit := Polynomial.SplittingField.splits (Polynomial.X ^ n - Polynomial.C (algebraMap R₀ K π) : Polynomial K)
    have hdeg : ((Polynomial.X ^ n - Polynomial.C (algebraMap R₀ K π) : Polynomial K).map (algebraMap K K')).degree ≠ 0 := by
      rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C hn0]
      exact_mod_cast hn0.ne'
    obtain ⟨θ, hθ⟩ := Polynomial.Splits.exists_eval_eq_zero hsplit hdeg
    have hθn : θ ^ n = algebraMap K K' (algebraMap R₀ K π) := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hθ
      exact hθ
    have hθint : IsIntegral R₀ θ := by
      refine ⟨Polynomial.X ^ n - Polynomial.C π, Polynomial.monic_X_pow_sub_C π hn0.ne', ?_⟩
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hθn,
        ← IsScalarTower.algebraMap_apply, sub_self]
    refine ⟨algebraMap B (Localization.AtPrime P) ⟨θ, hθint⟩, ?_⟩
    rw [halg]
    exact hθn

end S_IsDiscreteValuationRing_exists_dvr_extension_pow_eq
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_dvr_extension_pow_eq (solution)
