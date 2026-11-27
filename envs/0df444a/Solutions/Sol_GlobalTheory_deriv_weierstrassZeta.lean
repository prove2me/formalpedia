-- Prove2me | solution 1 for GlobalTheory.deriv_weierstrassZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:41.56326+00:00
-- url     : https://prove2.me/submissions/a065d0f6-6ec5-4ad4-9500-bc14afb7ca76

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
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (weierstrassZeta L) z = -℘[L] z := (hasDerivAt_weierstrassZeta L hz).deriv
end GlobalTheory
