-- Prove2me | solution 1 for GlobalTheory.sigmaSign_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.919185+00:00
-- url     : https://prove2.me/submissions/25ed0cdd-08e5-4e0c-86fc-a472e2a040d2

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
theorem _root_.solution (w : ℂ) : sigmaSign L w ≠ 0 := by
  unfold sigmaSign; split_ifs <;> simp
end GlobalTheory
