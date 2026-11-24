-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.c_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:46:32.217544+00:00
-- url     : https://prove2.me/submissions/335278bc-d488-47e1-96fa-713bd6a68090

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_ne_zero

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
theorem _root_.solution (x : X) : S.c x 0 = 1 := by
  have h := S.c_add_right x 0 0
  rw [add_zero] at h
  exact (mul_eq_left₀ (S.c_ne_zero x 0)).1 h.symm
end GlobalTheory.CompanionTheory.FinHeis.Sys
