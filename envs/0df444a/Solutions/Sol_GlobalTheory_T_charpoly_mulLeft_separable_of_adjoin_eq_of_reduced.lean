-- Prove2me | solution 1 for GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:59.564862+00:00
-- url     : https://prove2.me/submissions/b111d351-245c-45bc-9d95-83d58fa698d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Theorems.Thm_GlobalTheory_charpoly_mulLeft_separable_of_adjoin_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A → (LinearMap.mulLeft E y).charpoly.Separable := by
  first | exact @GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | exact GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | (intros; apply GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top <;> assumption)
end _root_.GlobalTheory.T
