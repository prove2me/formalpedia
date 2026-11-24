-- Prove2me | solution 1 for GlobalTheory.WeylDuality.eval_idFrame_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:48.946159+00:00
-- url     : https://prove2.me/submissions/e6646475-2411-4555-a3e2-ccd5b9681998

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) F) = ((eval (idFrame ℤ r n) F : ℤ) : ℚ) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, Int.cast_add]
  | mul_X p v hp =>
    simp only [map_mul, map_X, eval_X, hp, Int.cast_mul]
    congr 1
    unfold idFrame
    split_ifs <;> simp
end GlobalTheory.WeylDuality
