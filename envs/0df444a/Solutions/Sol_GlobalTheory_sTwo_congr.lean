-- Prove2me | solution 1 for GlobalTheory.sTwo_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:05.596215+00:00
-- url     : https://prove2.me/submissions/23a8c435-bdb9-44e9-8793-ca11c68fc6d3

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
theorem _root_.solution {L L' : PeriodPair} (h : L'.lattice = L.lattice) : sTwo L' = sTwo L := by
  simp only [sTwo, quasiPeriod_congr h]
end GlobalTheory
