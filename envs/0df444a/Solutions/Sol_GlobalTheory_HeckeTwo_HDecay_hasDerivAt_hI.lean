-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.hasDerivAt_hI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:53.039841+00:00
-- url     : https://prove2.me/submissions/5840359e-df2d-4720-9503-5d795435ee43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_sub_I_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) : HasDerivAt (hI y) (-(hI y t) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) - (y : ℂ) * I) 1 t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).sub_const ((y : ℂ) * I)
  refine (h1.inv (sub_I_ne hy t)).congr_deriv ?_
  simp [hI, div_eq_mul_inv, inv_pow]
end GlobalTheory.HeckeTwo.HDecay
