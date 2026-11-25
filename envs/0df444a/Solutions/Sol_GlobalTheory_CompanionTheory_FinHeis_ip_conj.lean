-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.ip_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:21.234418+00:00
-- url     : https://prove2.me/submissions/33b5c5ec-b39b-4c66-867c-b790eb1d6624

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
theorem _root_.solution (u v : M) : (starRingEnd ℂ) (ip S u v) = ip S v u := S.B_conj v u
end GlobalTheory.CompanionTheory.FinHeis
