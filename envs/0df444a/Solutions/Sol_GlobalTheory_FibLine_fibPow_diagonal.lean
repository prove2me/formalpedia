-- Prove2me | solution 1 for GlobalTheory.FibLine.fibPow_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:08:48.942178+00:00
-- url     : https://prove2.me/submissions/066fc0ac-78a0-4e18-99b6-b0db6a746c96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit
import Theorems.Thm_GlobalTheory_FibLine_eval_fibPow
import Theorems.Thm_GlobalTheory_FibLine_qMat_diagonal
import Theorems.Thm_GlobalTheory_FibLine_integral_comp_fsDens


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
theorem _root_.solution (a b : ℂ) (k : ℕ) : MvPolynomial.eval (entries (Matrix.diagonal ![a, b])) (fibPow k) =
    ∫ t in (0 : ℝ)..1, ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k := by
  rw [eval_fibPow]
  simp_rw [qMat_diagonal]
  exact integral_comp_fsDens (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) (by fun_prop)
end GlobalTheory.FibLine
