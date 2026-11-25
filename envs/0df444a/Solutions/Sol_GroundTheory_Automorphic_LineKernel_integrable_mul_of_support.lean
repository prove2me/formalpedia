-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integrable_mul_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:42.595137+00:00
-- url     : https://prove2.me/submissions/ee3941bd-00c9-4416-9ee1-db46e5d8342f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {φ K : ℝ → ℂ} (hφ : Continuous φ) (hK : Integrable K) {c : ℝ}
    (hs : support K ⊆ Icc 0 c) : Integrable fun u => φ u * K u := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 c) hφ.continuousOn
  refine Integrable.mono' (hK.norm.const_mul B) (hφ.aestronglyMeasurable.mul hK.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : K u = 0
  · simp [hu]
  · exact mul_le_mul_of_nonneg_right (hB u (hs hu)) (norm_nonneg _)
end GroundTheory.Automorphic.LineKernel
