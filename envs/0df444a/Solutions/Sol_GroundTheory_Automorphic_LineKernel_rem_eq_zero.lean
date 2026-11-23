-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.rem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:38.766796+00:00
-- url     : https://prove2.me/submissions/9aa1de37-4e87-4a5b-ac8b-fab885afed2f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_deriv_cutoff_eq_zero

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
theorem _root_.solution {a r t : ℝ} (hr : 0 < r) (ht : t ∉ Icc r (2 * r)) : rem a r t = 0 := by
  have := iteratedDeriv_deriv_cutoff_eq_zero hr ht 0
  simp only [iteratedDeriv_zero] at this
  simp [rem, this]
end GroundTheory.Automorphic.LineKernel
