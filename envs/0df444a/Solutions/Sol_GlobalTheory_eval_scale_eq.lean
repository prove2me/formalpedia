-- Prove2me | solution 1 for GlobalTheory.eval_scale_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:09.914258+00:00
-- url     : https://prove2.me/submissions/df59720e-c97d-4052-87d8-ae60c52f283e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ColumnDegreeLe

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
namespace GlobalTheory
theorem _root_.solution {K σ : Type*} [Field K] (w : σ → ℕ) (P : MvPolynomial σ K) (x : σ → K)
    (t : K) :
    eval (fun s => t ^ w s * x s) P =
      (∑ m ∈ P.support, Polynomial.monomial (∑ s ∈ m.support, w s * m s)
        (coeff m P * ∏ s ∈ m.support, x s ^ m s)).eval t := by
  rw [eval_eq, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  ring
end GlobalTheory
