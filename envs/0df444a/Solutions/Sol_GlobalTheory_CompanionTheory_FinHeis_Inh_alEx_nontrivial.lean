-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Inh.alEx_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:34.651054+00:00
-- url     : https://prove2.me/submissions/411b67cd-ddd3-4d21-b57b-310f46701957

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
open GlobalTheory.CompanionTheory.FinHeis.Inh
namespace GlobalTheory.CompanionTheory.FinHeis.Inh
theorem _root_.solution : ((1, 2) : ZMod 4 × ZMod 4) ∈ G₁ ∧ alEx (1, 2) = -1 ∧ alEx (1, 0) = 1 ∧ alEx (0, 2) = 1 := by
  refine ⟨by rw [mem_G₁]; decide, ?_, ?_, ?_⟩ <;> simp [alEx, e_two, e_zero]
end GlobalTheory.CompanionTheory.FinHeis.Inh
