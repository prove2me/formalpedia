-- Prove2me | solution 1 for GlobalTheory.T.exists_norm_weighted_least_squares_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:48.277205+00:00
-- url     : https://prove2.me/submissions/254f24ce-9935-4a0a-9c99-1b1997a9cd06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Theorems.Thm_GlobalTheory_WeightedLS_weighted_least_squares_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g → ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) → ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤ K * ‖b‖ := by
  first | exact @GlobalTheory.WeightedLS.weighted_least_squares_bound | exact GlobalTheory.WeightedLS.weighted_least_squares_bound | (intros; apply GlobalTheory.WeightedLS.weighted_least_squares_bound <;> assumption)
end _root_.GlobalTheory.T
