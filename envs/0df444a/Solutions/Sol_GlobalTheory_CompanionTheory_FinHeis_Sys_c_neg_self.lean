-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.c_neg_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:01:40.997711+00:00
-- url     : https://prove2.me/submissions/a62cffaf-3ee8-48aa-834a-e440194c38c9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_zero_right

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
open GlobalTheory.CompanionTheory.FinHeis.Sys
namespace GlobalTheory.CompanionTheory.FinHeis.Sys
theorem _root_.solution (x : X) : S.c x (-x) = 1 := by
  have h := S.c_add_right x x (-x)
  rw [add_neg_cancel, S.c_zero_right, S.c_self, one_mul] at h
  exact h.symm
end GlobalTheory.CompanionTheory.FinHeis.Sys
