-- Prove2me | solution 1 for GlobalTheory.finrank_mul_abs_norm_rpow_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:56.165893+00:00
-- url     : https://prove2.me/submissions/e29bb2d2-57f2-4755-90a4-136df082e2f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_card_mul_rpow_prod_le_sum
import Theorems.Thm_GlobalTheory_abs_norm_eq_prod_complexEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  rw [abs_norm_eq_prod_complexEmbeddings, ← Embeddings.card K ℂ]
  exact card_mul_rpow_prod_le_sum _ fun _ => norm_nonneg _
end GlobalTheory
