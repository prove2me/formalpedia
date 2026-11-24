-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.weierstrassSigma_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:55.281474+00:00
-- url     : https://prove2.me/submissions/6e186be4-9607-4f40-9637-4b2a298715cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_IsHomothetic_sigmaProd_mul

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
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : weierstrassSigma L' (c * z) = c * weierstrassSigma L z := by
  rw [weierstrassSigma, h.sigmaProd_mul, weierstrassSigma, mul_assoc]
end IsHomothetic
end GlobalTheory
