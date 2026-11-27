-- Prove2me | solution 2 for GlobalTheory.latticeForm_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:38:51.278522+00:00
-- url     : https://prove2.me/submissions/5a953ba1-b426-49a5-ba2b-95daa40e1b4f

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
theorem _root_.solution (u v : ℂ) : latticeForm L u v = inner ℂ v u / latticeArea L := by
  simp [latticeForm]
end GlobalTheory
