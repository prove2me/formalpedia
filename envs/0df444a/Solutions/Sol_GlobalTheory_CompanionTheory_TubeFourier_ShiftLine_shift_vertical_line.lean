-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:27.166569+00:00
-- url     : https://prove2.me/submissions/0197565a-4ca1-4883-a666-ca4d7688be3c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecay
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_ShiftLine_integral_vertical_line_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
namespace GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
theorem _root_.solution : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} →
    (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) →
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  intro Y _ _ _ f a b M hab hd hb
  exact integral_vertical_line_eq f a b M hab hd hb
end GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
