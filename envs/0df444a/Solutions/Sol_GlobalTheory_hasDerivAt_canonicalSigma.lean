-- Prove2me | solution 1 for GlobalTheory.hasDerivAt_canonicalSigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:43.983267+00:00
-- url     : https://prove2.me/submissions/cec4ac07-6a2a-4713-9f0c-bfbfd3568da5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
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
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (canonicalSigma L)
    ((weierstrassZeta L z - sTwo L * z) * canonicalSigma L z) z :=
  (hasDerivAt_canonicalSigma' L z).congr_deriv (by
    rw [(hasDerivAt_weierstrassSigma L hz).deriv, canonicalSigma]; ring)
end GlobalTheory
