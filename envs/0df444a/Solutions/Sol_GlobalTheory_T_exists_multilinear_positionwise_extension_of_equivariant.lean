-- Prove2me | solution 1 for GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:52.211091+00:00
-- url     : https://prove2.me/submissions/89d06d3d-c3e7-4cab-a936-c01485573cb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariantStatement
import Theorems.Thm_GlobalTheory_FactorwiseExtension_exists_multilinear_positionwise_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap ℂ H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap ℂ H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  first | exact @GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | exact GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | (intros; apply GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension <;> assumption)
end _root_.GlobalTheory.T
