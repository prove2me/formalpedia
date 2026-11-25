-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.climit_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:33.686483+00:00
-- url     : https://prove2.me/submissions/bb2b62d6-0c82-48b6-b058-3df01a003475

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_le_weight

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
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (p : ℕ) : climit (a := a) p ≤ weight M p :=
  ciSup_le fun n => coef_le_weight hε hg n p
end GroundTheory.Automorphic.LineKernel
