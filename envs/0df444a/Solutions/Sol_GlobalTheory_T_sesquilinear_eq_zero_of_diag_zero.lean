-- Prove2me | solution 1 for GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:14.961023+00:00
-- url     : https://prove2.me/submissions/889f818f-8fc2-49b7-a7f3-f6c50edeeb33

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Sesquilinear_eq_zero_of_diag_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v, B v v = 0) → B = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | exact GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero <;> assumption)
end _root_.GlobalTheory.T
