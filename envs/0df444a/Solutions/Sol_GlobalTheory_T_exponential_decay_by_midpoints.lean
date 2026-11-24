-- Prove2me | solution 1 for GlobalTheory.T.exponential_decay_by_midpoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:04.166225+00:00
-- url     : https://prove2.me/submissions/d5975240-cea3-4a7f-8db0-8660cade09a3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpoints
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpointsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_expDecay_of_midpoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X) (S : Set (ℝ × ℝ)), (∀ a ∈ S, ∀ g : T, ∃ r : ℝ, 0 < r ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - a.1| ≤ r → |x.2 - a.2| ≤ r → ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t)) → (∀ x : ℝ × ℝ, ∃ a ∈ S, ∃ b ∈ S, x = midpoint ℝ a b) → ExpDecay φ := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint | exact GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint <;> assumption)
end _root_.GlobalTheory.T
