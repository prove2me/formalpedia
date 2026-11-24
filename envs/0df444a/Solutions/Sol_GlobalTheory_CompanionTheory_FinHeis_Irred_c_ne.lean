-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Irred.c_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:37.264647+00:00
-- url     : https://prove2.me/submissions/88b08012-c989-4c3f-823d-fbb3ea04515b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.Irred
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
namespace GlobalTheory.CompanionTheory.FinHeis.Irred
theorem _root_.solution (x y : X) : S.c x y ≠ 0 := by
  intro h
  have := S.c_norm x y
  rw [h, norm_zero] at this
  exact zero_ne_one this
end GlobalTheory.CompanionTheory.FinHeis.Irred
