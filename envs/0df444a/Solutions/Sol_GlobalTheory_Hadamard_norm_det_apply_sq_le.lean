-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_det_apply_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:26:05.266435+00:00
-- url     : https://prove2.me/submissions/b7210880-dfb4-4c50-b942-0dfdd35f0cfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_det_sq_le_prod_row
import Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_nonneg
import Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_sum_smul
import Theorems.Thm_GlobalTheory_Hadamard_exists_orthonormal_of_linearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_sum_norm_apply_sq_le

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
theorem _root_.solution (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ^ 2 ≤ RCLike.re (gram 𝕜 x).det * ∏ j, ‖φ j‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    have h : (of fun j k => φ j (x k)) = (of fun j i => φ j (e i)) * m := by
      ext j k
      simp [hm, mul_apply, mul_comm]
    rw [h]
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he, det_mul, norm_mul, mul_pow,
      det_one, RCLike.one_re, mul_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_det_sq_le_prod_row _).trans ?_) (by positivity)
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => sum_norm_apply_sq_le he (φ j)
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hx
    have h0 : (of fun j k => φ j (x k)).det = 0 := by
      refine exists_mulVec_eq_zero_iff.mp ⟨g, fun h => hi (congrFun h i), ?_⟩
      funext j
      have := congrArg (φ j) hg
      simpa [mulVec, dotProduct, mul_comm] using this
    rw [h0, norm_zero]
    exact (by norm_num : (0 : ℝ) ^ 2 ≤ 0).trans
      (mul_nonneg (re_det_gram_nonneg x) (by positivity))
end GlobalTheory.Hadamard
