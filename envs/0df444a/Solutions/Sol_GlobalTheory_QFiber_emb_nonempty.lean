-- Prove2me | solution 1 for GlobalTheory.QFiber.emb_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:36.475626+00:00
-- url     : https://prove2.me/submissions/581fbce8-ca34-42e5-ba0b-b061c6bbc83b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
open GlobalTheory GlobalTheory.QFiber
open FractionalIdeal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.QFiber
theorem _root_.solution [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
end GlobalTheory.QFiber
