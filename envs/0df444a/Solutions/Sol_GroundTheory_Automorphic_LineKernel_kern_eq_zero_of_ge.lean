-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.kern_eq_zero_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:02.107881+00:00
-- url     : https://prove2.me/submissions/f0961d93-319d-408a-bd48-b5a786cc447c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
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
theorem _root_.solution {a r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ t) : kern a r t = 0 := by
  unfold kern indicator; split_ifs <;> simp [cutoff_eq_zero hr ht]
end GroundTheory.Automorphic.LineKernel
