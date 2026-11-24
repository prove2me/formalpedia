-- Prove2me | solution 1 for GlobalTheory.posSemidef_det_le_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:34.174825+00:00
-- url     : https://prove2.me/submissions/d98e4b93-9fae-4676-8fed-cf6110ea814f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Theorems.Thm_GlobalTheory_norm_det_sq_le_prod_col

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
theorem _root_.solution {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.nonneg
  have h := norm_det_sq_le_prod_col B
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜)] at h
  convert h using 1
  · rw [det_mul, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
    push_cast; rfl
  · push_cast
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [mul_apply, RCLike.conj_mul]
end GlobalTheory
