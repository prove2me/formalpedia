-- Prove2me | solution 1 for GlobalTheory.FibLine.eq_zero_of_eval_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:34.331969+00:00
-- url     : https://prove2.me/submissions/65f5c1b6-61fd-4904-a437-b3fa9f146dbc

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
theorem _root_.solution (P : MvPolynomial (Fin 2) ℂ) (h : ∀ a b : ℂ, MvPolynomial.eval ![a + b, a * b] P = 0) :
    P = 0 := by
  refine MvPolynomial.funext fun y => ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y 0 ^ 2 - 4 * y 1) two_pos
  have e : ![(y 0 + z) / 2 + (y 0 - z) / 2, (y 0 + z) / 2 * ((y 0 - z) / 2)] = y := by
    funext i
    fin_cases i
    · simp; ring
    · simp; linear_combination (-1 / 4 : ℂ) * hz
  simpa [e] using h ((y 0 + z) / 2) ((y 0 - z) / 2)
end GlobalTheory.FibLine
