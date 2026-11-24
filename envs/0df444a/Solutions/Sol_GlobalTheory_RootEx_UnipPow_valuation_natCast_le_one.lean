-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.valuation_natCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:33.895839+00:00
-- url     : https://prove2.me/submissions/392f5338-970b-48fa-839e-989ea6605456

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution (j : ℕ) : valuation k (j : k) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ]
    exact ((valuation k).map_add _ _).trans (max_le ih (by simp))
end GlobalTheory.RootEx.UnipPow
