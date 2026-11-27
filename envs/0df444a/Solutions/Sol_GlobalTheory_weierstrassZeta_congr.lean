-- Prove2me | solution 1 for GlobalTheory.weierstrassZeta_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:07.014554+00:00
-- url     : https://prove2.me/submissions/b0b227b3-7489-4acc-997f-c7cf74a8d7cf

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
theorem _root_.solution {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    weierstrassZeta L' = weierstrassZeta L := by
  ext z; simpa using (isHomothetic_one_iff.2 h).weierstrassZeta_mul z
end GlobalTheory
