-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.sigmaProd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:55.117811+00:00
-- url     : https://prove2.me/submissions/9615893c-a9f3-407f-8797-e3eed9be026e

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
namespace IsHomothetic
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (z : ℂ) :
    sigmaProd L' (c * z) = sigmaProd L z := by
  simp only [sigmaProd, sigmaFactor_eq]
  rw [← h.equiv.tprod_eq]
  simp only [IsHomothetic.coe_equiv, mul_div_mul_left _ _ h.ne_zero]
end IsHomothetic
end GlobalTheory
