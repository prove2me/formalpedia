-- Prove2me | solution 1 for GlobalTheory.analyticOrderAt_weierstrassSigma_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:44.249494+00:00
-- url     : https://prove2.me/submissions/fa0d550b-e3a2-4a42-8128-cc92dda001ae

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
    analyticOrderAt (weierstrassSigma L) z = 0 :=
  (analyticAt_weierstrassSigma L z).analyticOrderAt_eq_zero.2 (weierstrassSigma_ne_zero L hz)
end GlobalTheory
