-- Prove2me | solution 1 for GlobalTheory.posSemidef_re_det_le_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:21.404897+00:00
-- url     : https://prove2.me/submissions/7846ed33-46c3-48dd-b58b-fffd088cb5b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Theorems.Thm_GlobalTheory_posSemidef_det_le_prod_diag

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
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i) := by
  have h := posSemidef_det_le_prod_diag hA
  have h2 : ∏ i, A i i = ((∏ i, RCLike.re (A i i) : ℝ) : 𝕜) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    exact (hA.isHermitian.coe_re_apply_self i).symm
  rw [h2] at h
  simpa only [RCLike.ofReal_re] using (RCLike.le_iff_re_im.1 h).1
end GlobalTheory
