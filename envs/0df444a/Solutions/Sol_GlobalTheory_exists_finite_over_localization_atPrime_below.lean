-- Prove2me | solution 1 for GlobalTheory.exists_finite_over_localization_atPrime_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:21.405371+00:00
-- url     : https://prove2.me/submissions/ca81b29e-907b-461d-909a-e5bb51c90839

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConductorProdFstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomainStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsConductorAdicCompletionEssFiniteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (P B A : Type) [CommRing P] [CommRing B]
    [IsDomain B] [Algebra P B] [Module.Finite P B] [CommRing A] [IsLocalRing A] [Algebra B A]
    (𝔫 : Ideal B) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (hinj : Function.Injective (algebraMap P B)) :
    ∃ (p : Ideal P) (_ : p.IsPrime) (C : Type) (_ : CommRing C) (_ : IsDomain C)
      (_ : Algebra (Localization.AtPrime p) C) (_ : Module.Finite (Localization.AtPrime p) C)
      (_ : Algebra C A) (𝔪 : Ideal C) (_ : 𝔪.IsPrime),
      Function.Injective (algebraMap (Localization.AtPrime p) C) ∧ IsLocalization.AtPrime A 𝔪 ∧
        𝔪.comap (algebraMap (Localization.AtPrime p) C) = maximalIdeal (Localization.AtPrime p) := by
  classical
  let p : Ideal P := 𝔫.comap (algebraMap P B)
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  let M : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl
  have hMle : M ≤ 𝔫.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ h
    exact hs (Ideal.mem_comap.mpr h)
  have hM0 : M ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    show algebraMap P B s ∈ 𝔫
    rw [h0]
    exact 𝔫.zero_mem
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM0
  let algCA : Algebra (Localization M) A :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) A M 𝔫.primeCompl hMle
  have : IsScalarTower B (Localization M) A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  let 𝔪 : Ideal (Localization M) := (maximalIdeal A).comap (algebraMap (Localization M) A)
  have h𝔪 : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  have hNA : IsLocalization (𝔫.primeCompl.map (algebraMap B (Localization M))) A :=
    IsLocalization.isLocalization_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  have hunitB : ∀ b : B, IsUnit (algebraMap B A b) ↔ b ∈ 𝔫.primeCompl := fun b =>
    IsLocalization.AtPrime.isUnit_to_map_iff A 𝔫 b
  have hA : IsLocalization.AtPrime A 𝔪 := by
    refine IsLocalization.isLocalization_of_is_exists_mul_mem (S := A)
      (M := 𝔫.primeCompl.map (algebraMap B (Localization M))) (N := 𝔪.primeCompl) ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ h
      have hu : IsUnit (algebraMap B A b) := (hunitB b).mpr hb
      rw [IsScalarTower.algebraMap_apply B (Localization M) A] at hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h) hu
    · rintro ⟨x, hx⟩
      obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
      have key : algebraMap B A b =
          algebraMap B A s * algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s) := by
        rw [IsScalarTower.algebraMap_apply B (Localization M) A b,
          IsScalarTower.algebraMap_apply B (Localization M) A s, ← map_mul, IsLocalization.mk'_spec']
      refine ⟨algebraMap B (Localization M) s, b, ?_, (IsLocalization.mk'_spec' _ _ _).symm⟩
      have hs : IsUnit (algebraMap B A s) := (hunitB s).mpr (hMle s.2)
      have hx' : IsUnit (algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s)) := by
        by_contra hn
        exact hx (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
      refine (hunitB b).mp ?_
      rw [key]
      exact hs.mul hx'
  have hcomapB : 𝔪.comap (algebraMap B (Localization M)) = 𝔫 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal A 𝔫
  refine ⟨p, hp, Localization M, inferInstance, inferInstance, inferInstance, inferInstance, algCA,
    𝔪, h𝔪, ?_, hA, ?_⟩
  · exact localizationAlgebra_injective (S := B) (M := p.primeCompl) (Localization.AtPrime p)
      (Localization M) hinj
  · let Q : Ideal (Localization.AtPrime p) :=
      𝔪.comap (algebraMap (Localization.AtPrime p) (Localization M))
    have hQ : Q.comap (algebraMap P (Localization.AtPrime p)) = p := by
      show (𝔪.comap _).comap _ = p
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq P B (Localization M), ← Ideal.comap_comap, hcomapB]
    have h1 : Q = p.map (algebraMap P (Localization.AtPrime p)) := by
      have h2 := IsLocalization.map_under p.primeCompl (Localization.AtPrime p) Q
      rw [Ideal.under_def, hQ] at h2
      exact h2.symm
    show Q = _
    rw [h1]
    exact Localization.AtPrime.map_eq_maximalIdeal
end GlobalTheory
