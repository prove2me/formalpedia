-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.measurable_mulM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:49.941801+00:00
-- url     : https://prove2.me/submissions/6cb2d566-711c-4a02-8676-935d19573418

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
theorem _root_.solution {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → Fin m → Fin m → ℂ}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hu)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hv)
end GlobalTheory.GLFirstColumn
