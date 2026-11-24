-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.measurable_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:11.840812+00:00
-- url     : https://prove2.me/submissions/8378b084-354b-427c-943d-7f51aae006f8

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
theorem _root_.solution {k : ℕ} {α : Type*} [MeasurableSpace α] {u : α → Fin k → ℂ}
    {v : α → Fin k → Fin k → ℂ} (hu : Measurable u) (hv : Measurable v) :
    Measurable fun t => blk (u t) (v t) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · exact measurable_const
  · exact (measurable_pi_apply b).comp hu
  · exact measurable_const
  · exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hv)
end GlobalTheory.GLFirstColumn
