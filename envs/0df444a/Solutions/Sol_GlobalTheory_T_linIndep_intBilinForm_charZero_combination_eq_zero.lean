-- Prove2me | solution 1 for GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:18.849866+00:00
-- url     : https://prove2.me/submissions/4e6b495f-f1f7-46cd-999c-bf428277d442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinIndepIntBilinFormCharZeroCombinationEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinIndepIntBilinFormCharZeroCombinationEqZeroStatement
import Theorems.Thm_GlobalTheory_linIndep_intBilinForm_charZero_comb_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X) (k : Type) [Field k] [CharZero k] (a : Fin m → k), LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  first | exact @GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | exact GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | (intros; apply GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero <;> assumption)
end _root_.GlobalTheory.T
