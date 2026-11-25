-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.cutoff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:27.028341+00:00
-- url     : https://prove2.me/submissions/b5ff7c65-de99-46de-a6f1-b87fbd5dbe89

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
theorem _root_.solution (r t : ℝ) : cutoff r t ≤ 1 := by
  unfold cutoff; linarith [smoothTransition.nonneg (t / r - 1)]
end GroundTheory.Automorphic.LineKernel
