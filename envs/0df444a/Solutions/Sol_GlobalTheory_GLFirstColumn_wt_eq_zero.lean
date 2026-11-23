-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.wt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:09.83987+00:00
-- url     : https://prove2.me/submissions/9344dac8-4e5e-4330-92c0-ae31abc69630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons

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
theorem _root_.solution {m : ℕ} (a : Fin m → Fin m → ℂ) (ha : (Matrix.of a).det = 0) : wt a = 0 := by
  rcases m with _ | m
  · simp at ha
  · simp [wt, ha]
end GlobalTheory.GLFirstColumn
