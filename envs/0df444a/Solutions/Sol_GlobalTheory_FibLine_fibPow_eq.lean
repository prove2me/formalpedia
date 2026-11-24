-- Prove2me | solution 1 for GlobalTheory.FibLine.fibPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:30:59.980165+00:00
-- url     : https://prove2.me/submissions/d4895db1-6312-42fd-897c-86fa52dc75c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCompFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalFibPowExplicit
import Theorems.Thm_GlobalTheory_FibLine_eval_fibPow
import Theorems.Thm_GlobalTheory_FibLine_fibPow_diagonal
import Theorems.Thm_GlobalTheory_FibLine_eval_trDet
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_integral_qMat_unitary_conj
import Theorems.Thm_GlobalTheory_FibLine_eq_zero_of_eval_hermitian
import Theorems.Thm_GlobalTheory_FibLine_integral_affine_pow_eq_hPoly


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
theorem _root_.solution (k : ℕ) : fibPow k = (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval trDet (hPoly k) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_hermitian _ fun H hH => ?_
  have hR : MvPolynomial.eval (entries H) (MvPolynomial.aeval trDet (hPoly k)) =
      MvPolynomial.eval ![H.trace, H.det] (hPoly k) := by
    simpa [MvPolynomial.coe_aeval_eq_eval] using eval_trDet H (hPoly k)
  rw [map_sub, sub_eq_zero, MvPolynomial.smul_eval, hR, eval_fibPow]
  set l₀ := (hH.eigenvalues 0 : ℂ)
  set l₁ := (hH.eigenvalues 1 : ℂ)
  have hD : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) = Matrix.diagonal ![l₀, l₁] := by
    congr 1; funext i; fin_cases i <;> rfl
  have hs := hH.spectral_theorem
  rw [hD, Unitary.conjStarAlgAut_apply] at hs
  have htr : H.trace = l₀ + l₁ := by rw [hH.trace_eq_sum_eigenvalues, Fin.sum_univ_two]; rfl
  have hdet : H.det = l₀ * l₁ := by rw [hH.det_eq_prod_eigenvalues, Fin.prod_univ_two]; rfl
  rw [htr, hdet]
  conv_lhs => rw [hs]
  rw [UnitaryInv.integral_qMat_unitary_conj _ (hH.eigenvectorUnitary).2, ← eval_fibPow, fibPow_diagonal, integral_affine_pow_eq_hPoly]
  ring
end GlobalTheory.FibLine
