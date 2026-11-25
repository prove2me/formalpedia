-- Prove2me | solution 1 for GlobalTheory.QuadRefinement.isIntegral_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:13.071507+00:00
-- url     : https://prove2.me/submissions/77c83329-9eb7-4cac-8f17-252e5e0eb8b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsHomDivMulRefine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.QuadRefinement
variable {K : Type*} [Field K] [CharZero K] [StarRing K] {d : ℤ} {s : K}
omit [StarRing K]
namespace GlobalTheory.QuadRefinement
theorem _root_.solution (hd : d % 4 = 3) (hs : s ^ 2 = -(d : K)) :
    IsIntegral ℤ ((1 + s) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, d = 4 * k - 1 := ⟨(1 + d) / 4, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C k, by monicity!, ?_⟩
  rw [hk] at hs
  push_cast at hs
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [eq_intCast]
  linear_combination (1 / 4 : K) * hs
end GlobalTheory.QuadRefinement
