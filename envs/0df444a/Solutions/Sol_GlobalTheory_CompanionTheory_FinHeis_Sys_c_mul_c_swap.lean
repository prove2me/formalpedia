-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.c_mul_c_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:44.260337+00:00
-- url     : https://prove2.me/submissions/3300c320-f048-4338-ad6f-e35a7fc767b3

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
theorem _root_.solution (x y : X) : S.c x y * S.c y x = 1 := by
  have h := S.c_self (x + y)
  rw [S.c_add_left, S.c_add_right, S.c_add_right, S.c_self, S.c_self] at h
  simpa using h
end GlobalTheory.CompanionTheory.FinHeis.Sys
