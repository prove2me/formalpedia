-- Prove2me | solution 1 for GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:50.416566+00:00
-- url     : https://prove2.me/submissions/8910c07e-37ad-4c4a-93d0-569d579b70cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhaus
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhausStatement
import Theorems.Thm_GlobalTheory_SimilarTranspose_main
import Theorems.Thm_GlobalTheory_SymmetricSimilarTranspose_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k), ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  first | exact @GlobalTheory.SymmetricSimilarTranspose.main | exact GlobalTheory.SymmetricSimilarTranspose.main | (intros; apply GlobalTheory.SymmetricSimilarTranspose.main <;> assumption)
end _root_.GlobalTheory.T
