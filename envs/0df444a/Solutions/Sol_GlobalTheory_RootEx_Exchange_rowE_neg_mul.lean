-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.rowE_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:57:42.456056+00:00
-- url     : https://prove2.me/submissions/ce9ce2fb-b874-4f86-bae7-bf12e3724139

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
theorem _root_.solution (p : ℕ) (u : n → k) : rowE c p (-u) * rowE c p u = 1 := by
  ext1
  simp only [rowE, lowU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h]
end GlobalTheory.RootEx.Exchange
