-- Prove2me | solution 1 for GlobalTheory.SymShape.simpleSum_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:12.596534+00:00
-- url     : https://prove2.me/submissions/ef2a2a2d-8656-4a65-836a-7c0a7240fd48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SymmetricPositionLevelShapeOnParabolic
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.SymShape
namespace GlobalTheory.SymShape
theorem _root_.solution {F : Type} [Field F] {κ l : ℕ} (γ : GL (Fin κ) F) : simpleSum (embX l γ) = 0 := by
  apply GlobalTheory.RootEx.Radical.simpleSum_eq_zero
  intro i j
  rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.fromBlocks_apply₂₂]
end GlobalTheory.SymShape
