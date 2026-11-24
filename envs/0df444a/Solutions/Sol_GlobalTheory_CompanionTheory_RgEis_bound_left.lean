-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bound_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:57:39.038794+00:00
-- url     : https://prove2.me/submissions/a9149008-1494-410f-ae4f-a9f65923cf5d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    A * p * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hB hq]
end GlobalTheory.CompanionTheory.RgEis
