-- Prove2me | solution 1 for GlobalTheory.deriv_weierstrassSigma_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:37.987375+00:00
-- url     : https://prove2.me/submissions/fd081da2-b241-4519-a312-8a4e9ff7182f

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
theorem _root_.solution {w : ℂ} (hw : w ∈ L.lattice) :
    deriv (weierstrassSigma L) w = sigmaSign L w * cexp (quasiPeriod L w * (w / 2)) := by
  simpa [(hasDerivAt_weierstrassSigma_zero L).deriv] using
    deriv_weierstrassSigma_add_of_law L (weierstrassSigma_add L hw) (weierstrassSigma_zero L)
end GlobalTheory
