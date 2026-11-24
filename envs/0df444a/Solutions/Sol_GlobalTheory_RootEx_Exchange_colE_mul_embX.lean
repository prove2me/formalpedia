-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.colE_mul_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:43.990519+00:00
-- url     : https://prove2.me/submissions/b02cfcfd-c20b-4c29-8abb-85861857f8fa

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
    colE c p u * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
  have : colE c p (g.val.mulVec ((g⁻¹).val.mulVec u)) * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
    generalize (g⁻¹).val.mulVec u = w
    ext1
    simp only [colE, upU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_multiply]
    congr 1 <;> simp
    ext l s; by_cases h : s.val + 1 = p <;> simp [h, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
end GlobalTheory.RootEx.Exchange
