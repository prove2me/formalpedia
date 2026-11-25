-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.tendsto_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:09.432088+00:00
-- url     : https://prove2.me/submissions/0dd25d0d-9519-45d4-bb17-377d4354239c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_bddAbove_coef
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_mono


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
theorem _root_.solution (p : ℕ) : Tendsto (fun n => coef a n p) atTop (𝓝 (climit (a := a) p)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => coef_mono (fun j => (hg j).1) n p)
    (bddAbove_coef hε hg p)
end GroundTheory.Automorphic.LineKernel
