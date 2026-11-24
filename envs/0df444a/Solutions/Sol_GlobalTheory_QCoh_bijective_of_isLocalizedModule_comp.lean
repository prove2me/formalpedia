-- Prove2me | solution 1 for GlobalTheory.QCoh.bijective_of_isLocalizedModule_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:32.889136+00:00
-- url     : https://prove2.me/submissions/67b97127-c79c-4615-ad29-1c69af8cba54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {B M N : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [AddCommGroup N] [Module B N] (φ : M →ₗ[B] N) (s : Set B)
    (hs : Ideal.span s = ⊤) (P : s → Type*) [∀ b, AddCommGroup (P b)] [∀ b, Module B (P b)]
    (g : ∀ b, N →ₗ[B] P b) [∀ b : s, IsLocalizedModule.Away b.1 (g b)]
    [∀ b : s, IsLocalizedModule.Away b.1 (g b ∘ₗ φ)] : Function.Bijective φ := by
  refine bijective_of_isLocalized_span s hs P (fun b ↦ g b ∘ₗ φ) P g φ fun b ↦ ?_
  have : IsLocalizedModule.map (.powers b.1) (g b ∘ₗ φ) (g b) φ = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers b.1) (g b ∘ₗ φ) (g b) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id
end GlobalTheory.QCoh
