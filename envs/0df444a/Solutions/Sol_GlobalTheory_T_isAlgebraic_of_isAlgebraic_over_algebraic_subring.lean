-- Prove2me | solution 1 for GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:27.315174+00:00
-- url     : https://prove2.me/submissions/ccf9504c-8d68-40ac-9018-0c4cacf14e6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfSubringIsAlgebraic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfSubringIsAlgebraicStatement
import Theorems.Thm_GlobalTheory_isAlgebraic_of_subring_isAlgebraic


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
theorem _root_.solution : ∀ {L : Type} [Field L] [Algebra ℂ L] (S : Subalgebra ℂ L) (B : Subring L) (z : L),
  (∀ b ∈ B, IsAlgebraic S b) → IsAlgebraic B z → IsAlgebraic S z := by
  first | exact @GlobalTheory.isAlgebraic_of_subring_isAlgebraic | exact GlobalTheory.isAlgebraic_of_subring_isAlgebraic | (intros; apply GlobalTheory.isAlgebraic_of_subring_isAlgebraic <;> assumption)
end _root_.GlobalTheory.T
