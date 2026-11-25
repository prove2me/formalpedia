-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.ip_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:26.864468+00:00
-- url     : https://prove2.me/submissions/a4ae637d-4c5d-4a4b-9fc7-8a5c1f4c46ab

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
theorem _root_.solution (v : M) (hv : v ≠ 0) : 0 < (ip S v v).re := S.B_pos v hv
end GlobalTheory.CompanionTheory.FinHeis
