-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.LawLine.rho_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:17.725522+00:00
-- url     : https://prove2.me/submissions/7e2f5cfc-74c6-4534-a66b-62183625021e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_RationalFiniteIdeleFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_LawLine_c_mul_swap

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
theorem _root_.solution (S : Sys X M) (x y : X) (v : M) :
    S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by
  rw [S.9 x y v, S.9 y x v, smul_smul, add_comm y x]
  congr 1
  have h := GlobalTheory.CompanionTheory.FinHeis.LawLine.c_mul_swap S x y
  calc S.c x y = S.c x y * (S.c x y * S.c y x) := by rw [h, mul_one]
    _ = S.c x y ^ 2 * S.c y x := by ring
end GlobalTheory.CompanionTheory.FinHeis.LawLine
