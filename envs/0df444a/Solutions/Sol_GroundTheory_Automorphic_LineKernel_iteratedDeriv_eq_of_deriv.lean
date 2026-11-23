-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.iteratedDeriv_eq_of_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:01.39725+00:00
-- url     : https://prove2.me/submissions/04075662-2478-4fd5-a3ba-1455a3e96624

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds

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
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℕ → ℝ → E} (h : ∀ m, deriv (Φ m) = Φ (m + 1)) (m : ℕ) : iteratedDeriv m (Φ 0) = Φ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih, h]
end GroundTheory.Automorphic.LineKernel
