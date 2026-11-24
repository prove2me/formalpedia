-- Prove2me | solution 1 for GlobalTheory.RankFibre.X0_mul_X0_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:49.143839+00:00
-- url     : https://prove2.me/submissions/4f25ba17-3cfa-49b2-9b1b-5af5e48a37d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableFullRankFibre
import Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixFirstColumnBlock_mul_apply


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
theorem _root_.solution (k : Type) [Field k] (a b : ℕ) :
    GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) * (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))ᵀ = 1 := by
  ext i j
  rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
  simp [GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]
end GlobalTheory.RankFibre
