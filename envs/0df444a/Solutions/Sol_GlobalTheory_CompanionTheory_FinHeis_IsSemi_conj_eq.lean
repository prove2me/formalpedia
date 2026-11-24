-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.IsSemi.conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:40.714935+00:00
-- url     : https://prove2.me/submissions/66852e22-551f-4bb5-a3e4-9a32f475f7ba

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
theorem _root_.solution {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {x : X} (hx : x ∈ Γ) :
    (starRingEnd ℂ) (al x) = al x := by
  rcases h.1 x hx with e | e <;> rw [e] <;> simp
end IsSemi
end GlobalTheory.CompanionTheory.FinHeis
