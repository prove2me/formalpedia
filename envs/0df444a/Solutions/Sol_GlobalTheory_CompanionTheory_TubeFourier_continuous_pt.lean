-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.continuous_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:47:38.298817+00:00
-- url     : https://prove2.me/submissions/d06c6478-dac9-4d3f-b945-9c889b242c85

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBaseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformContinuousStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpointsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformLocallyBoundedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuousStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLinesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunctionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeChainHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  have h : (fun y : ℝ × ℝ => pt x y) =
      fun y => ((x.1 : ℂ) + (y.1 : ℂ) * Complex.I, (x.2 : ℂ) + (y.2 : ℂ) * Complex.I) := by
    funext y
    simp [pt, Complex.ext_iff]
  rw [h]
  fun_prop
end GlobalTheory.CompanionTheory.TubeFourier
