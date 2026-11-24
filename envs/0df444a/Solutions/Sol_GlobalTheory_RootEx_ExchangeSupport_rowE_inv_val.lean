-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.rowE_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:57:45.29381+00:00
-- url     : https://prove2.me/submissions/7a9bb328-12ed-42ff-aa16-7153e52de8ab

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
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution (u : n → k) : ((rowE c p u)⁻¹).val = fromBlocks 1 0 (-rowM c p u) 1 := rfl
end GlobalTheory.RootEx.ExchangeSupport
