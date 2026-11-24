-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.continuous_colM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:57:43.98134+00:00
-- url     : https://prove2.me/submissions/9b3c962e-58b4-4581-8f6f-bc3384a7d2c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation

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
omit [Fintype n] [DecidableEq n] [ValuativeRel k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution : Continuous fun u : n → k => colM c p u := by
  refine continuous_matrix fun i j => ?_
  simp only [colM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply i
  · exact continuous_const
end GlobalTheory.RootEx.ExchangeSupport
