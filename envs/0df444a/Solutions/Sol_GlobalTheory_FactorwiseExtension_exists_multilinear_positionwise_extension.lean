-- Prove2me | solution 1 for GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:18.305713+00:00
-- url     : https://prove2.me/submissions/0b58e48a-3f7d-4196-b037-9228a7425997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
import Theorems.Thm_GlobalTheory_FactorwiseExtension_invariant_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
namespace GlobalTheory.FactorwiseExtension
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
  intro ι _ _ H _ _ E _ _ A B hAB Rk Rg hRk hRg C hC hext huniq hpostC _hcomm hbs T₀ h0
  obtain ⟨T, hTa, -, hTc⟩ : ∃ T, GlobalTheory.FactorwiseExtension.Invariant A B Rk Rg C T₀ Finset.univ T := by
    refine Finset.induction_on (motive := fun s => ∃ T, GlobalTheory.FactorwiseExtension.Invariant A B Rk Rg C T₀ s T)
      Finset.univ ?_ ?_
    · refine ⟨T₀, fun u _ => rfl, ?_, ?_⟩
      · intro τ _ u hu r hr x hx
        exact h0 τ u (fun τ' h => by simpa [GlobalTheory.FactorwiseExtension.piecewiseSubmodule] using hu τ' h) r hr x hx
      · intro τ h
        simp at h
    · rintro τ₀ s hτ₀ ⟨T, hT⟩
      exact GlobalTheory.FactorwiseExtension.invariant_insert A B hAB Rk Rg hRk hRg C hC hext huniq hpostC hbs
        T₀ s τ₀ hτ₀ T hT
  refine ⟨T, hTa, fun τ u hu => hTc τ (Finset.mem_univ τ) u (fun τ' h => ?_)⟩
  simpa [GlobalTheory.FactorwiseExtension.piecewiseSubmodule] using hu τ' h
end GlobalTheory.FactorwiseExtension
