-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.gstab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:11.35115+00:00
-- url     : https://prove2.me/submissions/659430af-f9cc-462c-b1d2-54313233f385

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
namespace GlobalTheory.SigmaExtCount
theorem _root_.solution (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ↔ hM.lin ∈ compat g₁ g₂ hg₁ hg₂ := by
  constructor
  · intro h b
    obtain ⟨x, hx⟩ := hM.exists b
    rw [hM.lin_eq b hx, Submodule.mapQ_apply]
    exact hM.lin_eq ⟨g₂ b, hg₂ b.2⟩ (h _ hx)
  · intro h y hy
    obtain ⟨h2, e⟩ := (hM.mem_iff y).1 hy
    rw [hM.mem_iff]
    refine ⟨hg₂ h2, ?_⟩
    have := h ⟨y.2, h2⟩
    simp only at this
    rw [this, ← e, Submodule.mapQ_apply]
end GlobalTheory.SigmaExtCount
