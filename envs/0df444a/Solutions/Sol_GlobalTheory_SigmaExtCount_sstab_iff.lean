-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.sstab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:47:51.035792+00:00
-- url     : https://prove2.me/submissions/c487ac76-279a-4d9a-8b55-39bd379b20e7

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
theorem _root_.solution (hσ₂ : ∀ x, σ₂ (σ₂ x) = x) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ↔ twist hcc σ₁ σ₂ hs₁ hs₂ hM.lin = hM.lin := by
  constructor
  · intro h
    ext b
    rw [twist_apply]
    obtain ⟨x, hx⟩ := hM.exists ⟨σ₂ b, hs₂ b.2⟩
    rw [hM.lin_eq _ hx, Submodule.mapQ_apply]
    have := h _ hx
    simp only [hσ₂] at this
    exact (hM.lin_eq b this).symm
  · intro h y hy
    obtain ⟨h2, e⟩ := (hM.mem_iff y).1 hy
    rw [hM.mem_iff]
    refine ⟨hs₂ h2, ?_⟩
    simp only
    rw [← h, twist_apply]
    have hb : (⟨σ₂ (σ₂ y.2), hs₂ (hs₂ h2)⟩ : M₂) = ⟨y.2, h2⟩ := Subtype.ext (hσ₂ _)
    simp only [hb]
    rw [← e, Submodule.mapQ_apply]
end GlobalTheory.SigmaExtCount
