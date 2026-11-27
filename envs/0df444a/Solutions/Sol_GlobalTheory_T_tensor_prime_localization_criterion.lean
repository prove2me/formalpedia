-- Prove2me | solution 1 for GlobalTheory.T.tensor_prime_localization_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:51.447227+00:00
-- url     : https://prove2.me/submissions/92bfaf62-5178-4f09-9bce-1e964ece8266

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KrullLocal_smul_eq_zero_of_smul_one_tmul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KrullLocal.smul_eq_zero_of_smul_one_tmul_eq_zero | exact GlobalTheory.CompanionTheory.KrullLocal.smul_eq_zero_of_smul_one_tmul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.KrullLocal.smul_eq_zero_of_smul_one_tmul_eq_zero <;> assumption)
end _root_.GlobalTheory.T
