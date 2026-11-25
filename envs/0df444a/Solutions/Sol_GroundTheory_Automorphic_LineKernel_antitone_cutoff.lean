-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.antitone_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:22.238891+00:00
-- url     : https://prove2.me/submissions/e522a329-cfc4-456f-b271-6e4c9a3404d3

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
theorem _root_.solution {r : ℝ} (hr : 0 < r) : Antitone (cutoff r) := by
  intro s t hst
  unfold cutoff
  have : s / r - 1 ≤ t / r - 1 := by
    have := div_le_div_of_nonneg_right hst hr.le; linarith
  linarith [smoothTransition.monotone this]
end GroundTheory.Automorphic.LineKernel
