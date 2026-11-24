-- Prove2me | solution 1 for GlobalTheory.T.identity_as_sum_exp_minus_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:33.629227+00:00
-- url     : https://prove2.me/submissions/3ccbb079-30ae-46f1-97bf-1fabd1b16143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOneStatement
import Theorems.Thm_GlobalTheory_ExpDivision_exists_division


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ), (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  first | exact @GlobalTheory.ExpDivision.exists_division | exact GlobalTheory.ExpDivision.exists_division | (intros; apply GlobalTheory.ExpDivision.exists_division <;> assumption)
end _root_.GlobalTheory.T
