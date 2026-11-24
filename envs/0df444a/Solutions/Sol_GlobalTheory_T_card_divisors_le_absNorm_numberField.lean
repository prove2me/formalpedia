-- Prove2me | solution 1 for GlobalTheory.T.card_divisors_le_absNorm_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:53.966309+00:00
-- url     : https://prove2.me/submissions/451c1d1c-faef-4168-896f-4629ebf2de8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
import Theorems.Thm_GlobalTheory_card_le_absNorm_of_forall_le


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  first | exact @GlobalTheory.card_le_absNorm_of_forall_le | exact GlobalTheory.card_le_absNorm_of_forall_le | (intros; apply GlobalTheory.card_le_absNorm_of_forall_le <;> assumption)
end _root_.GlobalTheory.T
