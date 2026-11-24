-- Prove2me | solution 1 for GlobalTheory.KeyKa.discr_norm_eq_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:04.428382+00:00
-- url     : https://prove2.me/submissions/364d6c75-af5a-45af-8aae-1e0efc85524e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix
import Theorems.Thm_GlobalTheory_KeyKa_pointMatrix_mul_leftMulMatrix
import Theorems.Thm_GlobalTheory_KeyKa_trace_eq_sum_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution :
    ∀ (O B Ix : Type) [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Fintype Ix]
      [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)),
      (Matrix.of fun a a' => e a (β a')).det ≠ 0 →
        Algebra.discr O β = (Matrix.of fun a a' => e a (β a')).det ^ 2 ∧
          ∀ y : B, Algebra.norm O y = ∏ a, e a y := by
  intro O B Ix _ _ _ _ _ _ β e h
  refine ⟨?_, fun y => ?_⟩
  · have ht : Algebra.traceMatrix O β
        = (Matrix.of fun a a' => e a (β a')).transpose * (Matrix.of fun a a' => e a (β a')) := by
      ext i j
      rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_eq_sum_points β e h,
        Matrix.mul_apply]
      simp
    rw [Algebra.discr_def, ht, Matrix.det_mul, Matrix.det_transpose, sq]
  · have h1 := congrArg Matrix.det (pointMatrix_mul_leftMulMatrix β e y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h1
    rw [Algebra.norm_eq_matrix_det β]
    exact mul_right_cancel₀ h h1
end GlobalTheory.KeyKa
