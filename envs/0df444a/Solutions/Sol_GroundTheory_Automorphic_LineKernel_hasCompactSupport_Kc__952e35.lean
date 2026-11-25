-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.hasCompactSupport_Kc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:27.945344+00:00
-- url     : https://prove2.me/submissions/b8782f09-4d5f-4906-abb4-36ad5f158bd7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_Kc_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n : ℕ) : HasCompactSupport (Kc a r n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_Kc_subset ha hr n)
end GroundTheory.Automorphic.LineKernel
