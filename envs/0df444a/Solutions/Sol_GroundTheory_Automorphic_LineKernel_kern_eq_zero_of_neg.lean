-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.kern_eq_zero_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:01.994953+00:00
-- url     : https://prove2.me/submissions/652b9a30-9e1a-4220-bafe-94d99aa0cf4c

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
theorem _root_.solution {a r t : ℝ} (ht : t < 0) : kern a r t = 0 := by
  unfold kern; rw [indicator_of_notMem]; exact fun h => absurd (mem_Ici.1 h) (not_le.2 ht)
end GroundTheory.Automorphic.LineKernel
