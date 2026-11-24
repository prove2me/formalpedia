-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.inv_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:20.284274+00:00
-- url     : https://prove2.me/submissions/a7387113-f8b7-4e54-9069-ad05d88160e3

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
theorem _root_.solution {k : ℕ} (T : Fin k → ℂ) (m : Fin k → Fin k → ℂ) (hm : (Matrix.of m).det ≠ 0) :
    (Matrix.of (blk (-T) m))⁻¹ = Matrix.of (blk (T ᵥ* Matrix.of (invM m)) (invM m)) := by
  refine Matrix.inv_eq_right_inv ?_
  have h := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hm)
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · simp [blk, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct, Matrix.one_apply,
      (Fin.succ_ne_zero b).symm]
  · simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  · have := congrFun (congrFun h a) b
    simpa [blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, invM] using this
end GlobalTheory.GLFirstColumn
