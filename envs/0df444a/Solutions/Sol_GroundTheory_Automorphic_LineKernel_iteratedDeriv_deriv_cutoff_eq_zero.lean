-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.iteratedDeriv_deriv_cutoff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:35.324907+00:00
-- url     : https://prove2.me/submissions/e1724ccb-b91f-4272-9bfa-5093f1eaa73d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_zero

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
theorem _root_.solution {r t : ℝ} (hr : 0 < r) (ht : t ∉ Icc r (2 * r))
    (q : ℕ) : iteratedDeriv q (deriv (cutoff r)) t = 0 := by
  have hzero : deriv (cutoff r) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    rcases not_and_or.1 ht with h | h
    · push Not at h
      have hev : cutoff r =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with s hs using cutoff_eq_one hr (le_of_lt hs)
      filter_upwards [Iio_mem_nhds h] with s hs
      have hev' : cutoff r =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds hs] with u hu using cutoff_eq_one hr (le_of_lt hu)
      rw [hev'.deriv_eq]; simp
    · push Not at h
      filter_upwards [Ioi_mem_nhds h] with s hs
      have hev' : cutoff r =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hs] with u hu using cutoff_eq_zero hr (le_of_lt hu)
      rw [hev'.deriv_eq]; simp
  rw [hzero.iteratedDeriv_eq]; simp
end GroundTheory.Automorphic.LineKernel
