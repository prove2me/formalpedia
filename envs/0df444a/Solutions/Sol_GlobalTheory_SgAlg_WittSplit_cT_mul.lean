-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.cT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:36.217919+00:00
-- url     : https://prove2.me/submissions/172b0739-42cb-47da-9af7-e233ddb7445d

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
theorem _root_.solution {p q r : Type} [Fintype q] (A : Matrix p q E) (B : Matrix q r E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT; rw [Matrix.map_mul, Matrix.transpose_mul]
end GlobalTheory.SgAlg.WittSplit
