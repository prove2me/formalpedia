-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.contDiff_wF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:51:23.347747+00:00
-- url     : https://prove2.me/submissions/403aca01-7aaf-4fc3-909b-a4a58ec18f4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_wSpan_deriv
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_iteratedDeriv_mem

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
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) : ContDiff ℝ ∞ (wF σ y 0 0) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ => (wSpan_deriv hy (iteratedDeriv_mem hy m)).1
end GlobalTheory.HeckeTwo.HDecay
