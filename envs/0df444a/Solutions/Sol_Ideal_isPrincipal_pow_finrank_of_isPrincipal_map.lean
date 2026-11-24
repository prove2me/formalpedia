-- Prove2me | solution 1 for Ideal.isPrincipal_pow_finrank_of_isPrincipal_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:03.585561+00:00
-- url     : https://prove2.me/submissions/ebb4ae4e-7a12-4a32-b2bd-957bcd5e6f1c

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_Hilbert92
public import Theorems.Thm_algebraMap_injective_of_isIntegralClosure


set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
variable {K : Type} [Field K]
open Polynomial Module
variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]
variable [IsGalois K L]
namespace Ideal
theorem _root_.solution [IsDedekindDomain A] {I : Ideal A}
    (hI : (I.map (algebraMap A B)).IsPrincipal) : (I ^ finrank K L).IsPrincipal := by
  have : IsDomain B := Function.Injective.isDomain _ (IsIntegralClosure.algebraMap_injective B A L)
  have := IsIntegralClosure.isNoetherian A K L B
  have := IsIntegralClosure.isDedekindDomain A K L B
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAB := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraMap_injective_of_isIntegralClosure K L (R := A) (S := B))
  rw [IsFractionRing.finrank_eq A K B L, ← Ideal.relNorm_algebraMap,
    ← (I.map (algebraMap A B)).span_singleton_generator, Ideal.relNorm_singleton]
  exact ⟨⟨_, rfl⟩⟩
end Ideal
