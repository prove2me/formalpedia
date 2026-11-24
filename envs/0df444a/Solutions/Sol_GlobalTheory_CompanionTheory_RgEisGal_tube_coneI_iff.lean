-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.tube_coneI_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:27.698328+00:00
-- url     : https://prove2.me/submissions/2151abc3-e3f3-41d8-bce4-bb6804be11c2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneI r) ↔ r < m.2.re ∧ r < m.2.re + m.1.re :=
  Iff.rfl
end GlobalTheory.CompanionTheory.RgEisGal
