-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.kern_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:13.018475+00:00
-- url     : https://prove2.me/submissions/b7ab2b57-f4cf-4947-b2d8-fef1d96d23a8

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
theorem _root_.solution {a r t : ℝ} (ht : 0 ≤ t) : kern a r t = a * exp (-a * t) * cutoff r t := by
  unfold kern; rw [indicator_of_mem (mem_Ici.2 ht)]
end GroundTheory.Automorphic.LineKernel
