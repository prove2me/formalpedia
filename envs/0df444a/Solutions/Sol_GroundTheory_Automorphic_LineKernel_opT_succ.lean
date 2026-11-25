-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.opT_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:23.958326+00:00
-- url     : https://prove2.me/submissions/0c406eba-feaa-4e30-a818-4ab68a040601

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_sum_sc_succ

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
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) :
    opT a (n + 1) F u = opT a n F u -
      (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv (p + 1) F u :=
  sum_sc_succ a n fun p => iteratedDeriv p F u
end GroundTheory.Automorphic.LineKernel
