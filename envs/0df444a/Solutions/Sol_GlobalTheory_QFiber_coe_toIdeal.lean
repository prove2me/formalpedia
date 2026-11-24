-- Prove2me | solution 1 for GlobalTheory.QFiber.coe_toIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:35.669867+00:00
-- url     : https://prove2.me/submissions/21791e83-a628-4e3b-946a-d823f0698211

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
theorem _root_.solution {K : FractionalIdeal (𝓞 F)⁰ F} (h : K ≤ 1) :
    ((toIdeal K : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = K := by
  unfold toIdeal
  rw [dif_pos h]
  exact (le_one_iff_exists_coeIdeal.mp h).choose_spec
end GlobalTheory.QFiber
