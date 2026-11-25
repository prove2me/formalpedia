-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.deriv_cutoff_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:23.587799+00:00
-- url     : https://prove2.me/submissions/2c61b1f9-f4cf-43e5-99ee-6b01872fb1c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_antitone_cutoff

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
theorem _root_.solution {r : ℝ} (hr : 0 < r) (t : ℝ) : deriv (cutoff r) t ≤ 0 :=
  (antitone_cutoff hr).deriv_nonpos
end GroundTheory.Automorphic.LineKernel
