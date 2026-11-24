-- Prove2me | solution 1 for GlobalTheory.T.contour_shift_gaussian_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:10.418804+00:00
-- url     : https://prove2.me/submissions/e42ca22c-2d9c-49cb-a16f-2eb4e956071d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecay
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_ShiftLine_shift_vertical_line


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
theorem _root_.solution : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} → (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) → ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line | exact GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line <;> assumption)
end _root_.GlobalTheory.T
