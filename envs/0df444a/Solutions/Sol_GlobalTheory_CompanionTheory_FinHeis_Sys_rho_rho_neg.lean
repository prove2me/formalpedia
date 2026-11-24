-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.rho_rho_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:54.110337+00:00
-- url     : https://prove2.me/submissions/c5a6a888-9685-4df9-8056-f95029b2898d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_neg_self

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
theorem _root_.solution (x : X) (v : M) : S.rho x (S.rho (-x) v) = v := by
  rw [S.rho_rho, S.c_neg_self, add_neg_cancel, S.rho_zero, one_smul]
end GlobalTheory.CompanionTheory.FinHeis.Sys
