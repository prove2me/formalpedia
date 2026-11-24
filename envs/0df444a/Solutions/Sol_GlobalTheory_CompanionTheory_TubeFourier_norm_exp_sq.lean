-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.norm_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:42:54.614383+00:00
-- url     : https://prove2.me/submissions/b8dbe156-28eb-4bc0-9974-b990d8f79c53

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution (l : ℂ × ℂ) : ‖Complex.exp (l.1 ^ 2 + l.2 ^ 2)‖ =
    Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [sq]
  ring
end GlobalTheory.CompanionTheory.TubeFourier
