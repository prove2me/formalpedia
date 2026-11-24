-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.canonicalSigma_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:24:47.951427+00:00
-- url     : https://prove2.me/submissions/99745c96-e116-40a0-b03e-75f99d5db84f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_IsHomothetic_weierstrassSigma_mul

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
    (z : ℂ) : canonicalSigma L' (c * z) = c * canonicalSigma L z := by
  have := h.ne_zero
  rw [canonicalSigma, h.weierstrassSigma_mul, h.sTwo_eq, canonicalSigma, mul_assoc]
  congr 3
  field_simp
end IsHomothetic
end GlobalTheory
