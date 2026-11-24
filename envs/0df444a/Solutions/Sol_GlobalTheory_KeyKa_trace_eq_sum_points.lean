-- Prove2me | solution 1 for GlobalTheory.KeyKa.trace_eq_sum_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:24.282798+00:00
-- url     : https://prove2.me/submissions/98a1ed64-8a41-4d25-8f90-684cec2b6670

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix
import Theorems.Thm_GlobalTheory_KeyKa_pointMatrix_mul_leftMulMatrix

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
theorem _root_.solution {O B Ix : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O))
    (h : (Matrix.of fun a a' => e a (β a')).det ≠ 0) (y : B) :
    Algebra.trace O B y = ∑ a, e a y := by
  have h1 := pointMatrix_mul_leftMulMatrix β e y
  set P : Matrix Ix Ix O := Matrix.of fun a a' => e a (β a') with hP
  have h2 : P.det • Algebra.leftMulMatrix β y
      = P.adjugate * (Matrix.diagonal (fun a => e a y) * P) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have h3 := congrArg Matrix.trace h2
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_diagonal,
    smul_eq_mul, smul_eq_mul] at h3
  rw [Algebra.trace_eq_matrix_trace β]
  exact mul_left_cancel₀ h h3
end GlobalTheory.KeyKa
