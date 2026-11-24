-- Prove2me | solution 1 for GlobalTheory.DetFactor.map_transvection_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:41:01.257187+00:00
-- url     : https://prove2.me/submissions/bb5ef4f2-55e4-456d-aac4-71c947640208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Theorems.Thm_GlobalTheory_DetFactor_toGL_val
import Theorems.Thm_GlobalTheory_DetFactor_conj_transvection
import Theorems.Thm_GlobalTheory_DetFactor_det_diag2_ne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DetFactor.toGL_val

set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory.DetFactor
theorem _root_.solution (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) {i j : Fin n}
    (hij : i ≠ j) (t : k) : c (toGL (transvection i j t) (det_transvection_ne hij t)) = 1 := by
  set D := toGL _ (det_diag2_ne h2 i)
  have h1 : D * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) * D := by
    apply Units.ext; simp only [Units.val_mul, toGL_val, D]; exact conj_transvection hij t
  have h3 : toGL (transvection i j t) (det_transvection_ne hij t) * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) := by
    apply Units.ext; simp only [Units.val_mul, toGL_val]; rw [transvection_mul_transvection_same (h := hij), two_mul]
  have e1 := congrArg c h1
  have e3 := congrArg c h3
  rw [map_mul, map_mul, mul_comm (c D)] at e1
  have e1' := mul_right_cancel e1
  rw [map_mul, ← e1'] at e3
  exact (mul_eq_left.mp e3)
end GlobalTheory.DetFactor
