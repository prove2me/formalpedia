-- Prove2me | solution 1 for GlobalTheory.flat_of_surjective_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:40.47626+00:00
-- url     : https://prove2.me/submissions/be8fa015-9e22-40b7-a48e-578cf2e2415b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_exists_adicCompletion_ringEquiv
import Theorems.Thm_GlobalTheory_quotientMap_pow_bijective
import Theorems.Thm_GlobalTheory_flat_of_surjective_quotient_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
variable [IsNoetherianRing A] {φ : A →+* A}
namespace GlobalTheory
theorem _root_.solution {k : Type*} [CommRing k] [Algebra k A] [IsLocalRing A]
    (φ : A →ₐ[k] A) [IsLocalHom (φ : A →+* A)]
    (hle : maximalIdeal A ≤ (maximalIdeal A).comap φ)
    (h₀ : Function.Surjective (ResidueField.map (φ : A →+* A)))
    (h₁ : Function.Surjective (Ideal.mapCotangent _ _ φ hle)) :
    (∃ ψ : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal A) A,
      (∀ n x, AdicCompletion.evalₐ _ n (ψ x) =
        Ideal.quotientMap (maximalIdeal A ^ n) (φ : A →+* A) (pow_le_comap_pow_of_le hle n)
          (AdicCompletion.evalₐ _ n x)) ∧
      ∀ a, ψ (algebraMap A _ a) = algebraMap A _ (φ a)) ∧ (φ : A →+* A).Flat := by
  have h₀' : ∀ b, ∃ a, (φ : A →+* A) a - b ∈ maximalIdeal A := fun b => by
    obtain ⟨a, ha⟩ := h₀ (residue A b)
    obtain ⟨a, rfl⟩ := residue_surjective a
    exact ⟨a, Ideal.Quotient.eq.mp ha⟩
  have h₁' : ∀ y ∈ maximalIdeal A, ∃ x ∈ maximalIdeal A,
      (φ : A →+* A) x - y ∈ maximalIdeal A ^ 2 := fun y hy => by
    obtain ⟨x, hx⟩ := h₁ ((maximalIdeal A).toCotangent ⟨y, hy⟩)
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq] at hx
    exact ⟨x, x.2, hx⟩
  exact ⟨exists_adicCompletion_ringEquiv _ (quotientMap_pow_bijective hle h₀' h₁'),
    flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀' h₁'⟩
end GlobalTheory
