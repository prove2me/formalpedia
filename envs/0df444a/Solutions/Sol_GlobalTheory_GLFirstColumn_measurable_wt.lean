-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.measurable_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:01.999433+00:00
-- url     : https://prove2.me/submissions/c87d2eed-2e13-41e3-93f7-06c4cacf45ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_continuous_detM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {m : ℕ} : Measurable (wt : (Fin m → Fin m → ℂ) → ℝ≥0∞) :=
  (((continuous_detM.norm.measurable.pow_const 2).inv).pow_const m).ennreal_ofReal
end GlobalTheory.GLFirstColumn
