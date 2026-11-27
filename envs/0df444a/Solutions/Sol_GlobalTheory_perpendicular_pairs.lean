-- Prove2me | solution 1 for GlobalTheory.perpendicular_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:14.699074+00:00
-- url     : https://prove2.me/submissions/7a20e8ce-2ec2-4b8f-8285-f79587dc9602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_form_formPerpVector
import Theorems.Thm_GlobalTheory_formPerpVector_of_perp
import Theorems.Thm_GlobalTheory_formPerpVector_mem_subring
import Theorems.Thm_GlobalTheory_norm_det_formPairMatrix_le
import Theorems.Thm_GlobalTheory_norm_formPerpVector_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {p q : ℕ} :
    (∀ {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
      (h : M →ₗ[R] M →ₗ⋆[R] R) (e e' : Fin p → M) (g : Fin q → M),
      (∀ b c, h (formPerpVector h e e' (g b)) (e c) = 0) ∧
      (∀ (A : Subring R) (L : Submodule A M), (∀ a, e' a ∈ L) → (∀ b, g b ∈ L) →
        (∀ a a', h (e' a') (e a) ∈ A) → (∀ b a, h (g b) (e a) ∈ A) →
        ∀ b, formPerpVector h e e' (g b) ∈ L) ∧
      (∀ b, (∀ a, h (g b) (e a) = 0) →
        formPerpVector h e e' (g b) = (formPairMatrix h e e').det • g b)) ∧
    (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (e e' : Fin p → V) (g : Fin q → V) (r : ℝ),
      (∀ a, ‖e a‖ ≤ r) → (∀ a, ‖e' a‖ ≤ r) → (∀ b, ‖g b‖ ≤ r) →
      ‖(formPairMatrix (innerFormLeft V) e e').det‖ ≤ p ! * r ^ (2 * p) ∧
      ∀ b, ‖formPerpVector (innerFormLeft V) e e' (g b)‖ ≤ (p + 1)! * r ^ (2 * p + 1)) :=
  ⟨fun h e e' g => ⟨fun b c => form_formPerpVector h e e' (g b) c,
      fun A L he' hg he hv b => formPerpVector_mem_subring A L h e he' (hg b) he (hv b),
      fun _ hb => formPerpVector_of_perp h e e' hb⟩,
    fun e e' g _ he he' hg => ⟨norm_det_formPairMatrix_le e e' he he',
      fun b => norm_formPerpVector_le e e' (g b) he he' (hg b)⟩⟩
end GlobalTheory
