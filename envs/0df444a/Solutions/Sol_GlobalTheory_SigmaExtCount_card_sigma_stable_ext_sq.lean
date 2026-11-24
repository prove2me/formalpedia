-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:15:04.621682+00:00
-- url     : https://prove2.me/submissions/a158440c-4f09-434d-9731-46b81f23f28a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq
import Theorems.Thm_GlobalTheory_SigmaExtCount_card_stable_sq
import Theorems.Thm_GlobalTheory_SigmaExtCount_conjO_conjO
import Theorems.Thm_GlobalTheory_SigmaExtCount_sigmaSL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SigmaExtCount
open GlobalTheory.UnitLemma
namespace GlobalTheory.SigmaExtCount
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g →
    ∀ (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A), M₁ ∈ B₁.Lin → M₂ ∈ B₂.Lin →
    Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
      ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧
      M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ^ 2 =
    Nat.card {M : Submodule K.O (B₁.A × B₂.A) // (∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
      M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} := by
  intro K B₁ B₂ h1 h2 M₁ M₂ hM₁ hM₂
  obtain ⟨θ, θ', hθ, hδ⟩ := K.c_res
  have hθ' : conjO K θ = θ' := IsFractionRing.injective K.O K.E (by rw [algebraMap_conjO, hθ])
  have hu : IsUnit (θ - conjO K θ) := by
    rw [hθ']
    by_contra h
    exact hδ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
  have hmul : ∀ y : B₁.A × B₂.A, (B₁.g, B₂.g) * y =
      (LinearMap.mulLeft K.O B₁.g y.1, LinearMap.mulLeft K.O B₂.g y.2) := fun y => rfl
  have key := card_stable_sq (conjO_conjO K) θ hu (LinearMap.mulLeft K.O B₁.g)
    (LinearMap.mulLeft K.O B₂.g) (sigmaSL B₁) (sigmaSL B₂) (M₁ := M₁) (M₂ := M₂)
    (fun x hx => by simpa using hM₁.2.1 x hx) (fun x hx => by simpa using hM₂.2.1 x hx)
    (fun x hx => hM₁.2.2 x hx) (fun x hx => hM₂.2.2 x hx) B₁.σ_σ B₂.σ_σ
    (fun x => by simp [sigmaSL_apply, h1]) (fun x => by simp [sigmaSL_apply, h2])
  simp only [hmul]
  exact key
end GlobalTheory.SigmaExtCount
