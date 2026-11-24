-- Prove2me | solution 1 for GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:03.820862+00:00
-- url     : https://prove2.me/submissions/13c01230-00b7-439e-9085-a41ad902a12a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Theorems.Thm_GlobalTheory_HCA_integral_mul_dw_eq_neg_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)) (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  first | exact @GlobalTheory.HCA.integral_mul_dw_eq_neg_pow | exact GlobalTheory.HCA.integral_mul_dw_eq_neg_pow | (intros; apply GlobalTheory.HCA.integral_mul_dw_eq_neg_pow <;> assumption)
end _root_.GlobalTheory.T
