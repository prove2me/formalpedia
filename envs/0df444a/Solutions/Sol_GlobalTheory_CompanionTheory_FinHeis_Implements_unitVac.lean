-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Implements.unitVac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:35:53.428022+00:00
-- url     : https://prove2.me/submissions/325e9c11-136f-4a9a-bfed-0066b6794757

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_law

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
variable {S}
namespace GlobalTheory.CompanionTheory.FinHeis
namespace Implements
theorem _root_.solution {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) {al : X → ℂ} {Γ : AddSubgroup X}
    (hal : ∀ γ ∈ Γ, al (g γ) = al γ) {φ : M} (hφ : UnitVac S al Γ φ) :
    UnitVac S al (Γ.map g.toAddMonoidHom) (T φ) :=
  ⟨h.law hal hφ.1, by rw [h.2, hφ.2]⟩
end Implements
end GlobalTheory.CompanionTheory.FinHeis
