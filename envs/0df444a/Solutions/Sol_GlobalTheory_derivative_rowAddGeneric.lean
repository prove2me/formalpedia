-- Prove2me | solution 1 for GlobalTheory.derivative_rowAddGeneric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:16.5875+00:00
-- url     : https://prove2.me/submissions/a5f8307f-7ab7-4277-82e2-0dfa1287612e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm
import Theorems.Thm_GlobalTheory_rowAddGeneric_rowAddTerm
import Theorems.Thm_GlobalTheory_sum_X_mul_pderiv_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (u w : ι → σ) (huw : ∀ k l, u k ≠ w l)
    (P : MvPolynomial σ K) :
    Polynomial.derivative (rowAddGeneric u w P) =
      rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p s hp =>
    have h : ∑ k, X (u k) * pderiv (w k) (p * X s) =
        (∑ k, X (u k) * pderiv (w k) p) * X s + p * rowAddTerm K u w s := by
      rw [← sum_X_mul_pderiv_X, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [h, map_add, map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w),
      map_mul (rowAddGeneric u w), Polynomial.derivative_mul, hp,
      rowAddGeneric_rowAddTerm u w huw]
    have hX : Polynomial.derivative (rowAddGeneric u w (X s : MvPolynomial σ K)) =
        Polynomial.C (rowAddTerm K u w s) := by
      simp [rowAddGeneric]
    rw [hX]
end GlobalTheory
