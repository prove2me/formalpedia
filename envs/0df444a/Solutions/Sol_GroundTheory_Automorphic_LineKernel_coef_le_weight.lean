-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.coef_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:31.600752+00:00
-- url     : https://prove2.me/submissions/306eebfe-2d64-4848-b148-c8e96da9130f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_weight_pos
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_le_of


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
theorem _root_.solution (n p : ℕ) : coef a n p ≤ weight M p := by
  refine coef_le_of (fun j => (hg j).1) (by simp [weight]) (fun p => (weight_pos M p).le)
    (fun n p hp hpn => (hg n).2.1 p (Finset.mem_range.2 (by omega)) hp) n p
end GroundTheory.Automorphic.LineKernel
