-- Prove2me | solution 1 for GlobalTheory.SmoothPolynomialEvaluation.contDiff_evalFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:59.374385+00:00
-- url     : https://prove2.me/submissions/9177f331-c546-4071-95f4-d7ff3c56a64d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun
import Theorems.Thm_GlobalTheory_SmoothPolynomialEvaluation_contDiff_mvEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SmoothPolynomialEvaluation
namespace GlobalTheory.SmoothPolynomialEvaluation
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (evalFun p) := by
  have h : evalFun p = fun v => ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v
    unfold evalFun
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
    simp [Polynomial.coeff_map]
  rw [h]
  apply ContDiff.sum
  intro i _
  exact (contDiff_mvEval _).mul (contDiff_snd.pow i)
end GlobalTheory.SmoothPolynomialEvaluation
