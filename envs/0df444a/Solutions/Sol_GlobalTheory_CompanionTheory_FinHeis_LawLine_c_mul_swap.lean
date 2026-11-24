-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.LawLine.c_mul_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:44.325355+00:00
-- url     : https://prove2.me/submissions/cf0b58e0-20fa-4754-b9f2-cc36deffd847

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_RationalFiniteIdeleFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.LawLine
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.CompanionTheory.FinHeis.LawLine
theorem _root_.solution (S : Sys X M) (x y : X) : S.c x y * S.c y x = 1 := by
  have h := S.c_self (x + y)
  rw [S.c_add_left, S.c_add_right, S.c_add_right, S.c_self, S.c_self] at h
  simpa using h
end GlobalTheory.CompanionTheory.FinHeis.LawLine
