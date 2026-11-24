-- Prove2me | solution 1 for GlobalTheory.FibLine.qMat_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:39.450701+00:00
-- url     : https://prove2.me/submissions/c93f4b32-73f1-42cc-946e-66c9759d1f75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution (a b x : ℂ) : qMat (Matrix.diagonal ![a, b]) x =
    ((1 / (1 + ‖x‖ ^ 2) : ℝ) : ℂ) * a + (1 - ((1 / (1 + ‖x‖ ^ 2) : ℝ) : ℂ)) * b := by
  have h0 : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hx : x * starRingEnd ℂ x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [qMat, entries, Fintype.sum_prod_type, Fin.sum_univ_two, qCoef, lineVec, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, if_true, if_false, smul_zero, add_zero,
    zero_add, smul_eq_mul, map_one, mul_one, hx]
  simp
  left
  have h1 : (1 + (‖x‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h0
  field_simp
  ring
end GlobalTheory.FibLine
