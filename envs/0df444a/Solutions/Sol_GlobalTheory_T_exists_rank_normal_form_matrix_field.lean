-- Prove2me | solution 1 for GlobalTheory.T.exists_rank_normal_form_matrix_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:07.495352+00:00
-- url     : https://prove2.me/submissions/b589ca1c-33a0-457f-87e0-f1c60cbb46d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixFieldStatement
import Theorems.Thm_GlobalTheory_rank_normal_form_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  first | exact @GlobalTheory.rank_normal_form_field | exact GlobalTheory.rank_normal_form_field | (intros; apply GlobalTheory.rank_normal_form_field <;> assumption)
end _root_.GlobalTheory.T
