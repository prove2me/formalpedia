-- Prove2me | solution 1 for GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:44.474463+00:00
-- url     : https://prove2.me/submissions/cb10f6e1-6a33-46a5-a290-b9abc3deaa8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzShiftIteratedFDerivBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzShiftIteratedFDerivBoundStatement
import Theorems.Thm_GlobalTheory_schwartz_shift_iteratedFDeriv_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  first | exact @GlobalTheory.schwartz_shift_iteratedFDeriv_bound | exact GlobalTheory.schwartz_shift_iteratedFDeriv_bound | (intros; apply GlobalTheory.schwartz_shift_iteratedFDeriv_bound <;> assumption)
end _root_.GlobalTheory.T
