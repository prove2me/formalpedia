-- Prove2me | solution 1 for GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:08.949826+00:00
-- url     : https://prove2.me/submissions/6ad8ef68-7f1c-4777-8c8b-eafc74794dd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparableStatement
import Theorems.Thm_GlobalTheory_SimSep_conj_of_charpoly_eq_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [Field R] (m : ℕ) (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable → ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  first | exact @GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable <;> assumption)
end _root_.GlobalTheory.T
