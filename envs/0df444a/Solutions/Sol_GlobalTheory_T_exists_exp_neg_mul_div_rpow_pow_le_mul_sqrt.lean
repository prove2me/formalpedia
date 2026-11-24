-- Prove2me | solution 1 for GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:38.782851+00:00
-- url     : https://prove2.me/submissions/a1011ae2-10a8-4d6c-9899-62e71082e278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExpNegMulSqrtDivPowLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExpNegMulSqrtDivPowLeStatement
import Theorems.Thm_GlobalTheory_exp_neg_mul_sqrt_div_pow_le


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
theorem _root_.solution : ∀ (a : ℝ) (D : ℕ), 0 < a → ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) / (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.exp_neg_mul_sqrt_div_pow_le | exact GlobalTheory.exp_neg_mul_sqrt_div_pow_le | (intros; apply GlobalTheory.exp_neg_mul_sqrt_div_pow_le <;> assumption)
end _root_.GlobalTheory.T
