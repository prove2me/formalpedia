-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.measurable_kern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:15.223618+00:00
-- url     : https://prove2.me/submissions/f4c4e6d1-c3c6-4ff1-b1a4-75cc0aef6447

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_cutoff

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
theorem _root_.solution (a r : ℝ) : Measurable (kern a r) := by
  unfold kern
  exact (((continuous_const.mul (continuous_exp.comp (continuous_const.mul continuous_id))).mul
    (contDiff_cutoff r (n := 0)).continuous).measurable).indicator measurableSet_Ici
end GroundTheory.Automorphic.LineKernel
