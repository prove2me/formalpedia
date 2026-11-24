-- Prove2me | solution 1 for GlobalTheory.sum_log_norm_embedding_eq_finrank_mul_log_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:06.418791+00:00
-- url     : https://prove2.me/submissions/2778f7bf-3dc3-47c7-827e-136d0a227f87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Theorems.Thm_GlobalTheory_abs_norm_eq_absNorm_pow_of_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K M : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∑ σ : M →+* ℂ, Real.log ‖σ β‖ =
      (Module.finrank K M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  have h := abs_norm_eq_absNorm_pow_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have hp : ∏ σ : M →+* ℂ, ‖σ β‖ = ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod] at h3
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom M ℂ) (fun σ : M →+* ℂ => ‖σ β‖)
      (fun σ : M →ₐ[ℚ] ℂ => ‖σ β‖) (fun _ => rfl), ← h3]
    simp
  rw [← Real.log_prod (fun σ _ => by simpa using hβ), hp, h]
  push_cast
  rw [Real.log_pow]
end GlobalTheory
