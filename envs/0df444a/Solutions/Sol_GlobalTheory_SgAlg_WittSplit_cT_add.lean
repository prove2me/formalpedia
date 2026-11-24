-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.cT_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:28.711864+00:00
-- url     : https://prove2.me/submissions/59e24b19-0c56-42e6-81ef-1bdf127f6b4e

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
theorem _root_.solution {p q : Type} (A B : Matrix p q E) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j; simp [cT]
end GlobalTheory.SgAlg.WittSplit
