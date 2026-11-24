-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.rho_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:54.655929+00:00
-- url     : https://prove2.me/submissions/b7ee1a15-e025-4005-9485-fa43fd40007a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_rho_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_neg_rho

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
theorem _root_.solution (x : X) : Function.Bijective (S.rho x) :=
  Function.bijective_iff_has_inverse.2 ⟨S.rho (-x), S.rho_neg_rho x, S.rho_rho_neg x⟩
end GlobalTheory.CompanionTheory.FinHeis.Sys
