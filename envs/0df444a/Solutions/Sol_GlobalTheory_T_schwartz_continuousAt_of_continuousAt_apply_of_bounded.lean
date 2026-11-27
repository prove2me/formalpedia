-- Prove2me | solution 1 for GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:48.34485+00:00
-- url     : https://prove2.me/submissions/9d3d5c4b-861d-4aa1-b12a-41a1ef471459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBoundedStatement
import Theorems.Thm_GlobalTheory_schwartz_continuousAt_of_pointwise_of_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  first | exact @GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | exact GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | (intros; apply GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded <;> assumption)
end _root_.GlobalTheory.T
