-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.twist_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:07.629087+00:00
-- url     : https://prove2.me/submissions/c4253742-640d-434c-ad81-323f82505445

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
theorem _root_.solution (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x))
    {f : M₂ →ₗ[O] A₁ ⧸ M₁} (hf : f ∈ compat g₁ g₂ hg₁ hg₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f ∈ compat g₁ g₂ hg₁ hg₂ := by
  intro b
  rw [twist_apply, twist_apply]
  have hb : (⟨σ₂ (g₂ b), hs₂ (hg₂ b.2)⟩ : M₂) = ⟨g₂ (σ₂ b), hg₂ (hs₂ b.2)⟩ := Subtype.ext (hc₂ _)
  simp only [hb]
  rw [hf ⟨σ₂ b, hs₂ b.2⟩]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f ⟨σ₂ b, hs₂ b.2⟩)
  rw [← hx]
  simp only [Submodule.mapQ_apply, hc₁]
end GlobalTheory.SigmaExtCount
