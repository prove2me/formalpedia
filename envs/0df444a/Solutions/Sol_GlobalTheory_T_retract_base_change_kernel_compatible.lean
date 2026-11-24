-- Prove2me | solution 1 for GlobalTheory.T.retract_base_change_kernel_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:20.7768+00:00
-- url     : https://prove2.me/submissions/8e31aad1-22a0-4ce2-be85-7e24ed83e281

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatible
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatibleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Retract_constants_of_retract


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
theorem _root_.solution : ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  first | exact @GlobalTheory.CompanionTheory.Retract.constants_of_retract | exact GlobalTheory.CompanionTheory.Retract.constants_of_retract | (intros; apply GlobalTheory.CompanionTheory.Retract.constants_of_retract <;> assumption)
end _root_.GlobalTheory.T
