-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.conj_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:05:01.800917+00:00
-- url     : https://prove2.me/submissions/9763811f-0ff8-4db7-beb4-e9e5ac2e7b21

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
theorem _root_.solution (C : Matrix (Fin c) n k) (B : Matrix n (Fin c) k) (h : B * C = 0) :
    (lowU C * upU B * lowU (-C)).val = fromBlocks 1 B 0 (C * B + 1) := by
  simp [lowU, upU, fromBlocks_multiply, h, Matrix.add_mul, Matrix.mul_assoc]
end GlobalTheory.RootExchangeFixed
