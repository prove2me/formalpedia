-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.rowE_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:04.461007+00:00
-- url     : https://prove2.me/submissions/5e5d0cb4-d059-493b-8375-77c6688ff09e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_add

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
theorem _root_.solution : rowE c p (0 : n → k) = 1 := by
  have := rowE_add (c := c) (p := p) (0 : n → k) 0
  rw [add_zero] at this
  exact left_eq_mul.mp this
end GlobalTheory.RootEx.ExchangeSupport
