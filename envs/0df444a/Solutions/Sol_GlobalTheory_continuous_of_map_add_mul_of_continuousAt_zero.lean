-- Prove2me | solution 1 for GlobalTheory.continuous_of_map_add_mul_of_continuousAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:29.548072+00:00
-- url     : https://prove2.me/submissions/f5b4454c-8c7d-4d2e-8126-7aea2778d8c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHasDerivAtZeroOfMapAddMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ν : ℝ → ℂ)
    (hm : ∀ s t, ν (s + t) = ν s * ν t) (hc : ContinuousAt ν 0) : Continuous ν := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : ν = fun y => ν x * ν (y - x) := by
    funext y
    rw [← hm]
    congr 1
    ring
  rw [h1]
  refine continuousAt_const.mul ?_
  have h2 : ContinuousAt (fun y : ℝ => y - x) x := by fun_prop
  exact ContinuousAt.comp (f := fun y : ℝ => y - x) (by simpa using hc) h2
end GlobalTheory
