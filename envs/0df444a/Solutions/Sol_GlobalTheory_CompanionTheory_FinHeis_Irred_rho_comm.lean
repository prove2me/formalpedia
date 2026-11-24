-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Irred.rho_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:06.271378+00:00
-- url     : https://prove2.me/submissions/94ded730-8732-4553-a682-bded127efc47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_c_swap

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
theorem _root_.solution (x y : X) (v : M) :
    S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by
  rw [S.rho_rho, S.rho_rho, smul_smul, add_comm y x]
  congr 1
  linear_combination (-S.c x y) * c_swap S x y
end GlobalTheory.CompanionTheory.FinHeis.Irred
