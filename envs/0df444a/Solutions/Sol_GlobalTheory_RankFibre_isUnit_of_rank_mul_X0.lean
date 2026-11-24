-- Prove2me | solution 1 for GlobalTheory.RankFibre.isUnit_of_rank_mul_X0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:16.044249+00:00
-- url     : https://prove2.me/submissions/deef8816-c42c-49d3-9a9c-e5cba65c3d83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableFullRankFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.RankFibre
namespace GlobalTheory.RankFibre
theorem _root_.solution {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k)
    (h : (A * GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b))).rank = a) : IsUnit A := by
  have h1 : A.rank = Fintype.card (Fin a) := by
    refine le_antisymm (by simpa using A.rank_le_width) ?_
    simpa [h] using Matrix.rank_mul_le_left A (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))
  have hli : LinearIndependent k A.row := by
    rw [rank_eq_finrank_span_row] at h1
    rw [linearIndependent_iff_card_eq_finrank_span, eq_comm]; exact h1
  exact Matrix.linearIndependent_rows_iff_isUnit.1 hli
end GlobalTheory.RankFibre
