-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.integrable_gauss_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:04:05.251896+00:00
-- url     : https://prove2.me/submissions/c51603a2-31d3-42e7-9aaa-6f75bfaaa2a9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformBound
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_gauss_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one
end GlobalTheory.CompanionTheory.TubeFourier
