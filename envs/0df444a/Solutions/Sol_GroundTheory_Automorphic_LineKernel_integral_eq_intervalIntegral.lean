-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_eq_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:43.567438+00:00
-- url     : https://prove2.me/submissions/6923f210-283d-443b-906f-1b82e960cf83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {b : ℝ} (hb : 0 ≤ b) (hg : ∀ t ∉ Icc 0 b, g t = 0) :
    ∫ t, g t = ∫ t in (0 : ℝ)..b, g t := by
  rw [intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero hg]
end GroundTheory.Automorphic.LineKernel
