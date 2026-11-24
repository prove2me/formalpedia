-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.cT_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:38.236672+00:00
-- url     : https://prove2.me/submissions/5ec58206-b4a2-4f51-b7dd-d7c1758ec3f6

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {E : Type} [CommRing E] (σ : E →+* E)
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution {p : Type} [DecidableEq p] : cT σ (1 : Matrix p p E) = 1 := by
  unfold cT; rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
end GlobalTheory.SgAlg.WittSplit
