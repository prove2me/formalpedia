-- Prove2me | solution 1 for GlobalTheory.norm_det_sq_le_prod_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:14.339871+00:00
-- url     : https://prove2.me/submissions/aeca5238-50d2-4143-93c9-b8462218b8f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Theorems.Thm_GlobalTheory_det_gram_eq_normSq_det
import Theorems.Thm_GlobalTheory_det_gram_le_of_finrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  let v : ι → EuclideanSpace 𝕜 ι := fun j ↦ WithLp.toLp 2 fun i ↦ A i j
  have h := det_gram_le_of_finrank_eq (𝕜 := 𝕜) (by simp) v
  rw [det_gram_eq_normSq_det (EuclideanSpace.basisFun ι 𝕜), RCLike.ofReal_le_ofReal] at h
  have h2 : (EuclideanSpace.basisFun ι 𝕜).toBasis.det v = A.det := by
    rw [Basis.det_apply]; congr 1
  rw [h2] at h
  refine h.trans_eq (Finset.prod_congr rfl fun j _ ↦ ?_)
  rw [EuclideanSpace.norm_sq_eq]
end GlobalTheory
