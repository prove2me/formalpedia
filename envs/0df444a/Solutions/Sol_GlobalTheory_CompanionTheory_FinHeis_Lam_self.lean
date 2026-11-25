-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Lam_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:09.141858+00:00
-- url     : https://prove2.me/submissions/088a8f5d-bd87-40b2-95d5-faef8f47e6a7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_IsSemi_law_iff

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
theorem _root_.solution {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {φ : M} (hφ : Law S al Γ φ) :
    abelian₂ S al Γ Γ φ = φ := by
  have hsub : Subsingleton (Γ ⧸ Γ.addSubgroupOf Γ) := by
    rw [AddSubgroup.addSubgroupOf_self]; exact QuotientAddGroup.subsingleton_quotient_top
  letI : Unique (Γ ⧸ Γ.addSubgroupOf Γ) := uniqueOfSubsingleton 0
  rw [abelian₂, AddSubgroup.relIndex_self, la, finsum_unique, (h.law_iff φ).1 hφ _ (Subtype.prop _)]
  simp
end GlobalTheory.CompanionTheory.FinHeis
