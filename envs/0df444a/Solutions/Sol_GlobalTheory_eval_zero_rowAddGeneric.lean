-- Prove2me | solution 1 for GlobalTheory.eval_zero_rowAddGeneric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:10.642518+00:00
-- url     : https://prove2.me/submissions/229d3d8b-44db-4f9f-8cf1-5281220c0823

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm
import Theorems.Thm_GlobalTheory_eval_rowAddGeneric

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
theorem _root_.solution (u w : ι → σ) (P : MvPolynomial σ K) :
    Polynomial.eval 0 (rowAddGeneric u w P) = P := by
  have h := eval_rowAddGeneric u w (0 : K) P
  simpa using h
end GlobalTheory
