-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Implements.law
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:37.148993+00:00
-- url     : https://prove2.me/submissions/c4589a34-db91-4a0a-b064-2b4722df1cd8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam

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
    (hal : ∀ γ ∈ Γ, al (g γ) = al γ) {φ : M} (hφ : Law S al Γ φ) : Law S al (Γ.map g.toAddMonoidHom) (T φ) := by
  rintro _ ⟨γ, hγ, rfl⟩
  change S.rho (g γ) (T φ) = (al (g γ))⁻¹ • T φ
  rw [← h.1, hφ γ hγ, map_smul, hal γ hγ]
end Implements
end GlobalTheory.CompanionTheory.FinHeis
