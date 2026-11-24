-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.rowE_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:57:41.793359+00:00
-- url     : https://prove2.me/submissions/1035f89e-d617-4f78-a889-06ee431c5576

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((rowE c p u).val * M) (Sum.inr r) s =
      M (Sum.inr r) s + if r.val + 1 = p then ∑ t, u t * M (Sum.inl t) s else 0 := by
  by_cases h : r.val + 1 = p <;>
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]
end GlobalTheory.RootEx.Exchange
