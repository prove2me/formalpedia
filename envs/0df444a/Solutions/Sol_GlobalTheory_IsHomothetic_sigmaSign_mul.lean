-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.sigmaSign_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:53:59.866785+00:00
-- url     : https://prove2.me/submissions/4f3ba381-ebb2-4b90-9763-15e270d18dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
namespace IsHomothetic
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (w : ℂ) :
    sigmaSign L' (c * w) = sigmaSign L w := by
  classical
  unfold sigmaSign
  exact if_congr (by rw [mul_div_assoc, h (w / 2)]) rfl rfl
end IsHomothetic
end GlobalTheory
