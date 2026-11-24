-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.lowU_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:12.601942+00:00
-- url     : https://prove2.me/submissions/d94bddce-5533-42c7-b580-201fd37fa5d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution (C : Matrix (Fin c) n k) : lowU (-C) * lowU C = 1 := by
  ext1
  simp [lowU, fromBlocks_multiply]
end GlobalTheory.RootExchangeFixed
