-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.det_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:36.393467+00:00
-- url     : https://prove2.me/submissions/e488d8fb-7c59-41c1-a648-496fb042552e

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
theorem _root_.solution {k : ℕ} (r : Fin k → ℂ) (m : Fin k → Fin k → ℂ) :
    (Matrix.of (blk r m)).det = (Matrix.of m).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [blk, of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  congr 1
end GlobalTheory.GLFirstColumn
