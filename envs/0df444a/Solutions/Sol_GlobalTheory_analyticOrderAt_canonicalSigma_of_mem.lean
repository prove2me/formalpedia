-- Prove2me | solution 1 for GlobalTheory.analyticOrderAt_canonicalSigma_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:11.008814+00:00
-- url     : https://prove2.me/submissions/68e8bee6-769a-4da4-9fc4-96092a1cd054

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_canonicalSigma_eq_zero_iff
import Theorems.Thm_P2M_GlobalTheory_hasDerivAt_canonicalSigma__ab13341749ec

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
    analyticOrderAt (canonicalSigma L) w = 1 := by
  refine ((differentiable_canonicalSigma L).analyticAt
    w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((canonicalSigma_eq_zero_iff L).2 hw) ?_
  rw [(hasDerivAt_canonicalSigma' L w).deriv, (weierstrassSigma_eq_zero_iff L).2 hw, mul_zero,
    sub_zero]
  exact mul_ne_zero (deriv_weierstrassSigma_ne_zero L hw) (exp_ne_zero _)
end GlobalTheory
