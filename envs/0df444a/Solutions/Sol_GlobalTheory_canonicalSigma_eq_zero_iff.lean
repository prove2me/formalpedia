-- Prove2me | solution 1 for GlobalTheory.canonicalSigma_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:55.462799+00:00
-- url     : https://prove2.me/submissions/792636ec-b4b9-4bd4-bf5a-2aaf83233193

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
theorem _root_.solution {z : ℂ} : canonicalSigma L z = 0 ↔ z ∈ L.lattice := by
  rw [canonicalSigma, mul_eq_zero, or_iff_left (exp_ne_zero _), weierstrassSigma_eq_zero_iff]
end GlobalTheory
