-- Prove2me | solution 1 for GlobalTheory.Hadamard.re_det_gram_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:05.523491+00:00
-- url     : https://prove2.me/submissions/8ead5405-44b3-40fc-b5f2-fcd54cefcb86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_det_sq_le_prod_col
import Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_sum_smul
import Theorems.Thm_GlobalTheory_Hadamard_exists_orthonormal_of_linearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_sum_smul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.Hadamard
theorem _root_.solution (x : ι → E) : RCLike.re (gram 𝕜 x).det ≤ ∏ k, ‖x k‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he]
    simp only [det_one, RCLike.one_re, mul_one, norm_sum_smul_sq he]
    exact norm_det_sq_le_prod_col m
  · rw [← det_gram_ne_zero_iff_linearIndependent, not_not] at hx
    rw [hx, map_zero]
    positivity
end GlobalTheory.Hadamard
