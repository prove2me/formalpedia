-- Prove2me | solution 1 for GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:09.079801+00:00
-- url     : https://prove2.me/submissions/eb637b31-ca7a-4cb4-a214-6bc14ed39b98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBoundedStatement
import Theorems.Thm_GlobalTheory_GaussDerivBound_weighted_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  first | exact @GlobalTheory.GaussDerivBound.weighted_bound | exact GlobalTheory.GaussDerivBound.weighted_bound | (intros; apply GlobalTheory.GaussDerivBound.weighted_bound <;> assumption)
end _root_.GlobalTheory.T
