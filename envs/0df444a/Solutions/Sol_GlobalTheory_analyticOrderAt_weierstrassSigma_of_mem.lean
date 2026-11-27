-- Prove2me | solution 1 for GlobalTheory.analyticOrderAt_weierstrassSigma_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:40.418065+00:00
-- url     : https://prove2.me/submissions/ed9740e4-201e-45bb-9452-8b81bd3d8e23

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
    analyticOrderAt (weierstrassSigma L) w = 1 :=
  (analyticAt_weierstrassSigma L w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    ((weierstrassSigma_eq_zero_iff L).2 hw) (deriv_weierstrassSigma_ne_zero L hw)
end GlobalTheory
