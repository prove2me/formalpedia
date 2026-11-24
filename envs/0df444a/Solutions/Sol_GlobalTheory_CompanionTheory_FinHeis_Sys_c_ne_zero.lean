-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.c_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:00.082283+00:00
-- url     : https://prove2.me/submissions/40d170bd-03e3-45eb-9105-be47d7ab4e40

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
open GlobalTheory.CompanionTheory.FinHeis.Sys
namespace GlobalTheory.CompanionTheory.FinHeis.Sys
theorem _root_.solution (x y : X) : S.c x y ≠ 0 := by
  intro h
  have := S.c_norm x y
  rw [h] at this
  simp at this
end GlobalTheory.CompanionTheory.FinHeis.Sys
