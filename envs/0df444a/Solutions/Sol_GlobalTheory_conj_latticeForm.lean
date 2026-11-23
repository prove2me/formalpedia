-- Prove2me | solution 1 for GlobalTheory.conj_latticeForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:42.916838+00:00
-- url     : https://prove2.me/submissions/ac41a972-6fef-49cb-b079-c705c34e835b

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
theorem _root_.solution (u v : ℂ) : conj (latticeForm L u v) = latticeForm L v u := by
  simp [latticeForm, mul_comm]
end GlobalTheory
