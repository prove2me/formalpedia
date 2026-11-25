-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_norm_le_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:44.157059+00:00
-- url     : https://prove2.me/submissions/690c9b40-44b6-4416-a9f5-fb6c32d3dbad

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
theorem _root_.solution {f : ℝ → ℂ} (hf : Continuous f) {c D : ℝ} (hc : 0 ≤ c)
    (hs : support f ⊆ Icc 0 c) (hD : ∀ t ∈ Icc 0 c, ‖f t‖ ≤ D) : ∫ t, ‖f t‖ ≤ D * c := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc 0 c) fun t ht => by
    have : f t = 0 := by by_contra h; exact ht (hs h)
    simp [this]]
  calc ∫ t in Icc 0 c, ‖f t‖ ≤ ∫ t in Icc 0 c, D :=
        setIntegral_mono_on hf.norm.integrableOn_Icc (integrableOn_const (by simp) (by simp))
          measurableSet_Icc hD
    _ = D * c := by simp [hc, mul_comm]
end GroundTheory.Automorphic.LineKernel
