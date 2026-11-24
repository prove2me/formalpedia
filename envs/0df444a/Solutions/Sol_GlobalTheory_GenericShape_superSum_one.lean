-- Prove2me | solution 1 for GlobalTheory.GenericShape.superSum_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:12:39.30451+00:00
-- url     : https://prove2.me/submissions/11762638-3ae0-44c8-adbc-6341d4acd7d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.GenericShape
namespace GlobalTheory.GenericShape
theorem _root_.solution {F : Type} [Field F] {κ : ℕ} : superSum Fin.val (1 : Matrix (Fin κ) (Fin κ) F) = 0 := by
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
  split_ifs with e
  · rw [Matrix.one_apply_ne]; rintro rfl; omega
  · rfl
end GlobalTheory.GenericShape
