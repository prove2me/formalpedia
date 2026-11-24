-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.rho_neg_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:12.898702+00:00
-- url     : https://prove2.me/submissions/b930c01e-73d1-4281-a965-c59ad996b70a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_rho_neg

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
theorem _root_.solution (x : X) (v : M) : S.rho (-x) (S.rho x v) = v := by
  simpa using S.rho_rho_neg (-x) v
end GlobalTheory.CompanionTheory.FinHeis.Sys
