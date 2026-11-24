-- Prove2me | solution 1 for GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:13.444298+00:00
-- url     : https://prove2.me/submissions/b3f91e71-8864-471a-b310-fe6c004535fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRankStatement
import Theorems.Thm_GlobalTheory_exists_gl_mul_cols_eq_zero_of_rank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  first | exact @GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | exact GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | (intros; apply GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank <;> assumption)
end _root_.GlobalTheory.T
