-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.IsSemi.law_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:42.538246+00:00
-- url     : https://prove2.me/submissions/eb238a98-a382-477b-9ecf-ecb24fdc460a

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
namespace IsSemi
theorem _root_.solution {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) (φ : M) :
    Law S al Γ φ ↔ ∀ γ ∈ Γ, al γ • S.rho γ φ = φ := by
  refine ⟨fun hφ γ hγ => ?_, fun hφ γ hγ => ?_⟩
  · rw [hφ γ hγ, h.inv_eq hγ, smul_smul, h.mul_self hγ, one_smul]
  · rw [h.inv_eq hγ]
    conv_rhs => rw [← hφ γ hγ]
    rw [smul_smul, h.mul_self hγ, one_smul]
end IsSemi
end GlobalTheory.CompanionTheory.FinHeis
