-- Prove2me | solution 1 for GlobalTheory.latticeForm_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:55.364901+00:00
-- url     : https://prove2.me/submissions/9acc84c0-11c1-4bd1-bdeb-9a5ed2604a14

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
theorem _root_.solution (a u v : ℂ) :
    latticeForm L u (a * v) = conj a * latticeForm L u v := by
  simp only [latticeForm, map_mul]; ring
end GlobalTheory
