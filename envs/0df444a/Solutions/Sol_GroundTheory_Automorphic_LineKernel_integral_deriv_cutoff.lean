-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_deriv_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:31.064819+00:00
-- url     : https://prove2.me/submissions/d6f33375-9858-4484-b3bc-bdc6c2487682

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_cutoff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_deriv_cutoff_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_deriv_cutoff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_eq_intervalIntegral

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
theorem _root_.solution {r : ℝ} (hr : 0 < r) : ∫ t, deriv (cutoff r) t = -1 := by
  have hb : (0 : ℝ) ≤ 2 * r := by linarith
  rw [integral_eq_intervalIntegral hb]
  · rw [intervalIntegral.integral_deriv_eq_sub (fun t _ =>
        ((contDiff_cutoff r (n := 1)).differentiable one_ne_zero t))
      ((contDiff_deriv_cutoff r).continuous.intervalIntegrable _ _),
      cutoff_eq_zero hr le_rfl, cutoff_eq_one hr hr.le]
    norm_num
  · intro t ht
    have := iteratedDeriv_deriv_cutoff_eq_zero hr (fun h => ht ⟨hr.le.trans h.1, h.2⟩) 0
    simpa using this
end GroundTheory.Automorphic.LineKernel
