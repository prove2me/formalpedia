-- Prove2me | solution 1 for GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:56.17391+00:00
-- url     : https://prove2.me/submissions/855bc5ba-2928-4e98-8080-d51ce3596a9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartials
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasFDerivAtOfContinuousCoordinatePartials
import Theorems.Thm_GlobalTheory_hasFDerivAt_of_continuous_partials


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) →
      (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) →
      ∀ t, HasFDerivAt F
        (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  intro k F G hG hF t
  refine hasFDerivAt_of_continuous_partials k F G (fun i t => ?_) hG t
  have h0 : HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) (t i - t i) := by
    rw [sub_self]
    exact hF i t
  have h1 := h0.comp_sub_const (t i) (t i)
  have hfun : (fun s : ℝ => F (Function.update t i s)) =
      fun s : ℝ => F (t + (s - t i) • Pi.single i 1) := by
    funext s
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [hfun]
  exact h1
end GlobalTheory
