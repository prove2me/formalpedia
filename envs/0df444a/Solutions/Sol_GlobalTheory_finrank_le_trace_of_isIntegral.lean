-- Prove2me | solution 1 for GlobalTheory.finrank_le_trace_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:43.58159+00:00
-- url     : https://prove2.me/submissions/4330490d-f898-47e4-8b31-a7da6cde6b62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_finrank_le_sum_norm_of_isIntegral
import Theorems.Thm_GlobalTheory_trace_eq_sum_realEmbeddings
import Theorems.Thm_GlobalTheory_sum_abs_realEmbeddings
import Theorems.Thm_GlobalTheory_ne_zero_of_totallyPos

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
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory
theorem _root_.solution {a : F} (hi : IsIntegral ℤ a)
    (ha : ∀ σ : F →+* ℝ, 0 < σ a) : (finrank ℚ F : ℚ) ≤ Algebra.trace ℚ F a := by
  have h := finrank_le_sum_norm_of_isIntegral hi (ne_zero_of_totallyPos ha)
  rw [← sum_abs_realEmbeddings, Finset.sum_congr rfl fun σ _ => abs_of_pos (ha σ),
    ← trace_eq_sum_realEmbeddings] at h
  exact_mod_cast h
end GlobalTheory
