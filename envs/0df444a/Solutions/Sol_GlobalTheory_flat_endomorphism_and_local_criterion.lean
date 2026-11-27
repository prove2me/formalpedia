-- Prove2me | solution 1 for GlobalTheory.flat_endomorphism_and_local_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:30.069365+00:00
-- url     : https://prove2.me/submissions/c22714b9-b9e1-47b0-9447-3ed589007c8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_flat_of_flat_residueField_baseChange_dvr
import Theorems.Thm_GlobalTheory_exists_adicCompletion_ringEquiv
import Theorems.Thm_GlobalTheory_quotientMap_pow_bijective
import Theorems.Thm_GlobalTheory_flat_of_surjective_quotient_sq
import Theorems.Thm_GlobalTheory_flat_of_flat_baseChange
import Theorems.Thm_GlobalTheory_ideal_eq_bot_of_flat_quotient

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
namespace GlobalTheory
theorem _root_.solution :
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (φ : A →+* A) [IsLocalHom φ],
      Function.Surjective (ResidueField.map φ) →
      (∀ y ∈ maximalIdeal A, ∃ x ∈ maximalIdeal A, φ x - y ∈ maximalIdeal A ^ 2) →
      (∃ ψ : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal A) A,
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) (a : A),
          AdicCompletion.evalₐ _ n x = Ideal.Quotient.mk _ a →
            AdicCompletion.evalₐ _ n (ψ x) = Ideal.Quotient.mk _ (φ a)) ∧
        ∀ a, ψ (algebraMap A _ a) = algebraMap A _ (φ a)) ∧ φ.Flat) ∧
    (∀ (T A B : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing A]
      [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra T A] [Algebra T B]
      [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B] (φ : A →ₐ[T] B),
      (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
        ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat → (φ : A →+* B).Flat) ∧
    (∀ (k K A B : Type u) [CommRing k] [CommRing K] [Algebra k K] [Module.FaithfullyFlat k K]
      [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B),
      (Algebra.TensorProduct.map (AlgHom.id k K) φ : K ⊗[k] A →+* K ⊗[k] B).Flat →
        (φ : A →+* B).Flat) ∧
    (∀ (T R : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing R]
      [IsDomain R] [IsDiscreteValuationRing R] [Algebra T R] [IsLocalHom (algebraMap T R)]
      (J : Ideal R), J ≠ ⊤ → Module.Flat T (R ⧸ J) → J = ⊥) := by
  refine ⟨fun A _ _ _ φ _ h₀ h₁ => ?_,
    fun T A B _ _ _ _ _ _ _ _ _ _ _ _ φ h => flat_of_flat_residueField_baseChange_dvr φ h,
    fun k K A B _ _ _ _ _ _ _ _ φ h => flat_of_flat_baseChange K φ h,
    fun T R _ _ _ _ _ _ _ _ J hJ _ => ideal_eq_bot_of_flat_quotient T hJ⟩
  have hle : maximalIdeal A ≤ (maximalIdeal A).comap φ := ((local_hom_TFAE φ).out 0 3).mp ‹_›
  have h₀' : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A := fun b => by
    obtain ⟨a, ha⟩ := h₀ (residue A b)
    obtain ⟨a, rfl⟩ := residue_surjective a
    exact ⟨a, Ideal.Quotient.eq.mp ha⟩
  obtain ⟨ψ, hψ, hψ'⟩ := exists_adicCompletion_ringEquiv _ (quotientMap_pow_bijective hle h₀' h₁)
  exact ⟨⟨ψ, fun n x a h => by rw [hψ, h, Ideal.quotientMap_mk], hψ'⟩,
    flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀' h₁⟩
end GlobalTheory
