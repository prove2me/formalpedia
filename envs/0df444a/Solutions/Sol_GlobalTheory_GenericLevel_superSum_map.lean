-- Prove2me | solution 1 for GlobalTheory.GenericLevel.superSum_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:23.815015+00:00
-- url     : https://prove2.me/submissions/01c96384-3597-4c2f-a378-ab9a0ee682e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.GenericLevel
variable {F a : Type} [Field F] [Fintype a] [DecidableEq a]
omit [DecidableEq a]
namespace GlobalTheory.GenericLevel
theorem _root_.solution {R : Type} [CommRing R] (f : R →+* F) (pos : a → ℕ) (M : Matrix a a R) :
    superSum pos (M.map f) = f (∑ r, ∑ s, if pos s = pos r + 1 then M r s else 0) := by
  unfold superSum
  simp only [map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp
end GlobalTheory.GenericLevel
