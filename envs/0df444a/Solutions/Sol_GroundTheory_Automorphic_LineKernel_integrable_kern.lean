-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integrable_kern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:35.287098+00:00
-- url     : https://prove2.me/submissions/5174b4a0-72b0-4ade-b964-e82771c1d12a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_kern_subset
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_measurable_kern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) : Integrable (kern a r) := by
  have hon : IntegrableOn (kern a r) (Icc 0 (2 * r)) := by
    refine Measure.integrableOn_of_bounded (M := a) (measure_Icc_lt_top).ne
      (measurable_kern a r).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg ha r t)]; exact kern_le ha r t
  refine hon.integrable_of_forall_notMem_eq_zero fun t ht => ?_
  by_contra h; exact ht (support_kern_subset hr h)
end GroundTheory.Automorphic.LineKernel
