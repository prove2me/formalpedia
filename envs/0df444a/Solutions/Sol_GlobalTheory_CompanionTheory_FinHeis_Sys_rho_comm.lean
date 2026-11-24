-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Sys.rho_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:47.697815+00:00
-- url     : https://prove2.me/submissions/ec41378f-b194-40b0-b526-17003ab53aba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_mul_c_swap

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
theorem _root_.solution (x y : X) (v : M) : S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by
  rw [S.rho_rho, S.rho_rho, smul_smul, add_comm y x]
  congr 1
  linear_combination (-(S.c x y)) * S.c_mul_c_swap x y
end GlobalTheory.CompanionTheory.FinHeis.Sys
