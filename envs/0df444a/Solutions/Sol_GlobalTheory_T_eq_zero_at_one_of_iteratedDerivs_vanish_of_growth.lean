-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:02.641639+00:00
-- url     : https://prove2.me/submissions/de252aac-3258-4c86-93c6-cc72ca2a3886

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroAtOneOfIteratedDerivsVanishOfGrowth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by
  first | exact @GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | exact GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | (intros; apply GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth <;> assumption)
end _root_.GlobalTheory.T
