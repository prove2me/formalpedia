-- Prove2me | solution 1 for GlobalTheory.AutQuotCheck.cls_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:06.913951+00:00
-- url     : https://prove2.me/submissions/944d8001-8946-43e1-8804-8c5e9fb2aa4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.AutQuotCheck
variable {G : Type} [Group G] (Γ : Subgroup G)
open MeasureTheory
open scoped Pointwise
variable {G : Type} [Group G] (Γ : Subgroup G)
namespace GlobalTheory.AutQuotCheck
namespace _root_.GlobalTheory.AutQuotCheck
theorem _root_.solution (g g' : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ g = _root_.GlobalTheory.AutQuotCheck.cls Γ g' ↔ ∃ γ ∈ Γ, g' = γ * g := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]
  constructor
  · intro h
    exact ⟨g' * g⁻¹, h, by group⟩
  · rintro ⟨γ, hγ, rfl⟩
    simpa using hγ
end _root_.GlobalTheory.AutQuotCheck
end GlobalTheory.AutQuotCheck
