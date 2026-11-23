-- Prove2me | solution 1 for GlobalTheory.abs_im_latticeForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:32.646496+00:00
-- url     : https://prove2.me/submissions/5061ba3d-825d-4389-8af8-5133417fad88

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
theorem _root_.solution : |(latticeForm L L.ω₂ L.ω₁).im| = 1 := by
  rw [latticeForm, div_ofReal_im, abs_div, abs_of_pos (latticeArea_pos L), mul_comm,
    ← latticeArea_eq, div_self (latticeArea_pos L).ne']
end GlobalTheory
