-- Prove2me | solution 1 for GlobalTheory.T.isRat_of_hankel_eventually_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:09.178581+00:00
-- url     : https://prove2.me/submissions/16f3a080-6114-4e38-847a-ec253309bd2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZeroStatement
import Theorems.Thm_GlobalTheory_Nef_isRat_of_hankel_eventually_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ), (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  first | exact @GlobalTheory.Nef.isRat_of_hankel_eventually_zero | exact GlobalTheory.Nef.isRat_of_hankel_eventually_zero | (intros; apply GlobalTheory.Nef.isRat_of_hankel_eventually_zero <;> assumption)
end _root_.GlobalTheory.T
