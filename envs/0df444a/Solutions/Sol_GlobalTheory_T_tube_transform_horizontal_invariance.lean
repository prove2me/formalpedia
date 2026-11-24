-- Prove2me | solution 1 for GlobalTheory.T.tube_transform_horizontal_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:45.444324+00:00
-- url     : https://prove2.me/submissions/42127266-592c-4743-974e-7caf516aabb7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvariance
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvarianceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_phi_shift_fst


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
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst <;> assumption)
end _root_.GlobalTheory.T
