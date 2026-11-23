-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.kern_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:08.897049+00:00
-- url     : https://prove2.me/submissions/061ff435-71f9-47cd-8e2f-e5bf671d206c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_nonneg

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) (r t : ℝ) : 0 ≤ kern a r t := by
  unfold kern indicator
  split_ifs
  · exact mul_nonneg (mul_nonneg ha (exp_pos _).le) (cutoff_nonneg r t)
  · exact le_rfl
end GroundTheory.Automorphic.LineKernel
