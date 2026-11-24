-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bound_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:57:39.795005+00:00
-- url     : https://prove2.me/submissions/1e66b20a-4a71-4852-b959-f13308173440

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
    B * q * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hA hp]
end GlobalTheory.CompanionTheory.RgEis
