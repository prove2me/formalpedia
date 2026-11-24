-- Prove2me | solution 1 for GlobalTheory.T.inverse_transform_holomorphic_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:14:57.251429+00:00
-- url     : https://prove2.me/submissions/5b8600a5-f79c-4049-9450-c5da2edd3230

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLines
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLinesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_inv_differentiable_line


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
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line | exact GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line <;> assumption)
end _root_.GlobalTheory.T
