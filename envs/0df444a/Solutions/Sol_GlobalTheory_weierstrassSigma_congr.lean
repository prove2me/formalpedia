-- Prove2me | solution 1 for GlobalTheory.weierstrassSigma_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:04.14005+00:00
-- url     : https://prove2.me/submissions/9ca7f6a2-6eff-4040-b935-4e6aefa02ce4

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
theorem _root_.solution {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    weierstrassSigma L' = weierstrassSigma L := by
  ext z; simpa using (isHomothetic_one_iff.2 h).weierstrassSigma_mul z
end GlobalTheory
