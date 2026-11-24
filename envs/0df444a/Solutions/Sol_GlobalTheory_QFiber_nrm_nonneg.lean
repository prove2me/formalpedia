-- Prove2me | solution 1 for GlobalTheory.QFiber.nrm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:37.240155+00:00
-- url     : https://prove2.me/submissions/724e9b4f-9958-45e2-8e4b-25803d27b56c

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
theorem _root_.solution (𝔞 : Frac F) : 0 ≤ nrm 𝔞 := by
  unfold nrm; exact_mod_cast absNorm_nonneg _
end GlobalTheory.QFiber
