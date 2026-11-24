-- Prove2me | solution 1 for GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:56.947497+00:00
-- url     : https://prove2.me/submissions/f37a5a73-4ca2-4a12-a4c5-5072de724092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
theorem _root_.solution (z : ℝ) :
    ‖Complex.exp (z * I) - 1 - z * I‖ ≤ 3 * z ^ 2 := by
  have hn : ‖(z : ℂ) * I‖ = |z| := by simp
  rcases le_or_gt |z| 1 with hz | hz
  · have := Complex.norm_exp_sub_one_sub_id_le (x := (z : ℂ) * I) (by rw [hn]; exact hz)
    rw [hn, sq_abs] at this
    nlinarith [sq_nonneg z]
  · calc ‖Complex.exp (z * I) - 1 - z * I‖
        ≤ ‖Complex.exp (z * I)‖ + ‖(1 : ℂ)‖ + ‖(z : ℂ) * I‖ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ = 2 + |z| := by rw [Complex.norm_exp_ofReal_mul_I, hn]; norm_num
      _ ≤ 3 * z ^ 2 := by
        have : |z| ^ 2 = z ^ 2 := sq_abs z
        nlinarith
end GlobalTheory.CharFormDeriv
