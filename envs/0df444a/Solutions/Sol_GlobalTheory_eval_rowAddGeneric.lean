-- Prove2me | solution 1 for GlobalTheory.eval_rowAddGeneric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:01.766821+00:00
-- url     : https://prove2.me/submissions/dd8d416c-a960-4bfc-9d21-086ef4b19659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm

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
theorem _root_.solution (u w : ι → σ) (t : K) (P : MvPolynomial σ K) :
    Polynomial.eval (C t) (rowAddGeneric u w P) =
      bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    simp [rowAddGeneric, rowAddTerm, Finset.mul_sum, Polynomial.eval_finsetSum]
    simp only [mul_comm]
end GlobalTheory
