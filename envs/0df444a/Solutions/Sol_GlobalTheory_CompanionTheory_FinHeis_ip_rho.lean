-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.ip_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:34.555196+00:00
-- url     : https://prove2.me/submissions/f25bc9fc-7455-4398-9873-907c4babc97b

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
namespace GlobalTheory.CompanionTheory.FinHeis
theorem _root_.solution (x : X) (u v : M) : ip S (S.rho x u) (S.rho x v) = ip S u v := S.B_rho x v u
end GlobalTheory.CompanionTheory.FinHeis
