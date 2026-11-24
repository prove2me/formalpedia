-- Prove2me | solution 1 for GlobalTheory.WittTrace.linearIndependent_col_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:48.7409+00:00
-- url     : https://prove2.me/submissions/dd241767-4d6d-4348-bfbf-b07a3a910d50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
namespace GlobalTheory.WittTrace
theorem _root_.solution {K : Type*} [Field K] {n a : ℕ}
    {X : Matrix (Fin n) (Fin a) K} (h : X.rank = a) : LinearIndependent K X.col := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_cols] at h
  exact h.symm
end GlobalTheory.WittTrace
