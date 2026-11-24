-- Prove2me | solution 1 for GlobalTheory.FibLine.eval_fibPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:51:01.079953+00:00
-- url     : https://prove2.me/submissions/5a7b25d1-bddc-42e4-9b2b-a7ae64cc0a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit
import Theorems.Thm_GlobalTheory_FibLine_Intg_integrable_prod_qCoef_mul_fsDens


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
theorem _root_.solution (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    MvPolynomial.eval (entries H) (fibPow k) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by
  have e : ∀ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) =
      ∑ f : Fin k → Fin 2 × Fin 2, (∏ i, qCoef x (f i)) * (fsDens x : ℂ) * ∏ i, entries H (f i) := by
    intro x
    rw [qMat, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [smul_eq_mul, Finset.prod_mul_distrib]
    ring
  simp only [fibPow, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  simp_rw [e]
  rw [integral_finset_sum _ fun f _ => ((Intg.integrable_prod_qCoef_mul_fsDens k f).mul_const _)]
  simp only [integral_mul_const]
end GlobalTheory.FibLine
