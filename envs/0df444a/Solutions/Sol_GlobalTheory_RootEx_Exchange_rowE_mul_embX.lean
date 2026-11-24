-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.rowE_mul_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:57:40.212713+00:00
-- url     : https://prove2.me/submissions/99d1080d-cbff-4159-b2e7-1ff04325485c

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
theorem _root_.solution (p : ℕ) (u : n → k) (g : GL n k) :
    rowE c p u * embX c g = embX c g * rowE c p (g.valᵀ.mulVec u) := by
  ext1
  simp only [rowE, lowU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
    fromBlocks_multiply]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]
end GlobalTheory.RootEx.Exchange
