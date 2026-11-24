-- Prove2me | solution 1 for GlobalTheory.T.tube_transform_independent_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:00.788183+00:00
-- url     : https://prove2.me/submissions/b8d093c5-5a3f-40bc-8741-14b42d3ffd57

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBase
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBaseStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_phi_eq_of_convex


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
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω → ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | exact GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex <;> assumption)
end _root_.GlobalTheory.T
