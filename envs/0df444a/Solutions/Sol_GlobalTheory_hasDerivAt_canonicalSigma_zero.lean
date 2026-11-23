-- Prove2me | solution 1 for GlobalTheory.hasDerivAt_canonicalSigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:24.273595+00:00
-- url     : https://prove2.me/submissions/fca34690-aa88-4be9-871e-1c0818616df0

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
theorem _root_.solution : HasDerivAt (canonicalSigma L) 1 0 := by
  simpa [(hasDerivAt_weierstrassSigma_zero L).deriv] using hasDerivAt_canonicalSigma' L 0
end GlobalTheory
