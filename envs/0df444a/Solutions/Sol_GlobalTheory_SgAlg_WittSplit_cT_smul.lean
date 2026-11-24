-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.cT_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:39.088316+00:00
-- url     : https://prove2.me/submissions/5a2f3e42-ca23-45d4-8766-38bf718ebea9

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
theorem _root_.solution {p q : Type} (c : E) (A : Matrix p q E) : cT σ (c • A) = σ c • cT σ A := by
  ext i j; simp [cT]
end GlobalTheory.SgAlg.WittSplit
