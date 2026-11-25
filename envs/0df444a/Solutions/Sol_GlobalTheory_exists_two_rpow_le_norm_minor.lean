-- Prove2me | solution 1 for GlobalTheory.exists_two_rpow_le_norm_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:03.880655+00:00
-- url     : https://prove2.me/submissions/279a65ba-8da9-48f7-9771-85045061c421

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_two_rpow_neg_half_le_choose_rpow
import Theorems.Thm_GlobalTheory_exists_choose_rpow_le_norm_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
namespace GlobalTheory
theorem _root_.solution (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by
  obtain ⟨hi, S, hS⟩ := exists_choose_rpow_le_norm_minor A hA
  exact ⟨S, (two_rpow_neg_half_le_choose_rpow hi hr).trans hS⟩
end GlobalTheory
