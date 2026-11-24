-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.continuous_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:06.157914+00:00
-- url     : https://prove2.me/submissions/35d1ff83-0fbf-473c-a187-31b355833164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_rowM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ExchangeSupport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution : Continuous fun u : n → k => rowE c p u := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_rowM continuous_const
  · exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_rowM.neg continuous_const
end GlobalTheory.RootEx.ExchangeSupport
