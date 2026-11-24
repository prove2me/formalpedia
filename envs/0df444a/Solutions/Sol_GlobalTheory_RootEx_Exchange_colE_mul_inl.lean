-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.colE_mul_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:44.710797+00:00
-- url     : https://prove2.me/submissions/8ac4eced-f47c-4fba-a6d5-6e40ffc8f337

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
theorem _root_.solution (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((colE c (P.val + 1) u).val * M) (Sum.inl r) s = M (Sum.inl r) s + u r * M (Sum.inr P) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]
end GlobalTheory.RootEx.Exchange
