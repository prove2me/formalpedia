-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.measurable_invM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:50.053814+00:00
-- url     : https://prove2.me/submissions/0e6c1109-3f4b-4c67-bede-904dfa88a1a9

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
theorem _root_.solution {m : ℕ} :
    Measurable (invM : (Fin m → Fin m → ℂ) → Fin m → Fin m → ℂ) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hof : Continuous fun x : Fin m → Fin m → ℂ =>
    (Matrix.of x : Matrix (Fin m) (Fin m) ℂ) := continuous_id
  have h1 : Measurable fun x : Fin m → Fin m → ℂ => (Matrix.of x).det := hof.matrix_det.measurable
  have h2 : Measurable fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate i j :=
    (hof.matrix_adjugate.matrix_elem i j).measurable
  simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact h1.inv.mul h2
end GlobalTheory.GLFirstColumn
