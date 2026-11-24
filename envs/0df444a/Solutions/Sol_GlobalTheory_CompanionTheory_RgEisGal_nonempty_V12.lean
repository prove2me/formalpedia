-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.nonempty_V12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:01:28.532311+00:00
-- url     : https://prove2.me/submissions/47bbb753-3f40-497e-bd8c-c609fa2a254f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour

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
theorem _root_.solution (M : ℝ) : (chamberPairTwoThree M).Nonempty :=
  ⟨(-3 * M - 3, 2 * M + 2), by simp only [chamberPairTwoThree, Set.mem_setOf_eq]; constructor <;> linarith⟩
end GlobalTheory.CompanionTheory.RgEisGal
