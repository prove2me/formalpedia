-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.isUnit_det_of_coercive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:55.714033+00:00
-- url     : https://prove2.me/submissions/0212a5bb-54e0-4a12-9f78-379ab01b6996

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_le_of_coercive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound
namespace GlobalTheory.WeightedInverseBound
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) : IsUnit Y.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h := norm_le_of_coercive hc hY (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
end GlobalTheory.WeightedInverseBound
