-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.twist_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:09.194958+00:00
-- url     : https://prove2.me/submissions/9090c403-85d3-4c82-96d0-b931c7d9fa65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq

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
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}
variable (hcc : ∀ o, cO (cO o) = o) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
  (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)
namespace GlobalTheory.SigmaExtCount
theorem _root_.solution (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (f : M₂ →ₗ[O] A₁ ⧸ M₁) : twist hcc σ₁ σ₂ hs₁ hs₂ (twist hcc σ₁ σ₂ hs₁ hs₂ f) = f := by
  ext b
  rw [twist_apply, twist_apply]
  have hb : (⟨σ₂ (σ₂ b), hs₂ (hs₂ b.2)⟩ : M₂) = b := Subtype.ext (hσ₂ _)
  simp only [hb]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f b)
  rw [← hx, Submodule.mapQ_apply, Submodule.mapQ_apply, hσ₁]
end GlobalTheory.SigmaExtCount
