-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.mul_colE_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:49.231341+00:00
-- url     : https://prove2.me/submissions/31c7fb2b-0920-4641-b7e0-6030155ce798

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
theorem _root_.solution (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (colE c p u).val) r (Sum.inr s) =
      M r (Sum.inr s) + if s.val + 1 = p then ∑ t, M r (Sum.inl t) * u t else 0 := by
  by_cases h : s.val + 1 = p <;>
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]
end GlobalTheory.RootEx.Exchange
