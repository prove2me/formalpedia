-- Prove2me | solution 1 for GlobalTheory.logDeriv_weierstrassSigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:22.193689+00:00
-- url     : https://prove2.me/submissions/7103a53d-4a1c-4c38-9424-901496bdb944

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
    logDeriv (weierstrassSigma L) z = weierstrassZeta L z := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassSigma L hz).deriv,
    mul_div_cancel_right₀ _ (weierstrassSigma_ne_zero L hz)]
end GlobalTheory
