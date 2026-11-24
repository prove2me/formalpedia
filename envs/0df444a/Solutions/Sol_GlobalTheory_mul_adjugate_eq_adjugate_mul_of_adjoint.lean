-- Prove2me | solution 1 for GlobalTheory.mul_adjugate_eq_adjugate_mul_of_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:32.507411+00:00
-- url     : https://prove2.me/submissions/90fe1a11-a08e-4c7a-bbb2-ecf718f4182c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Kronecker
open GlobalTheory
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]
namespace GlobalTheory
theorem _root_.solution (B P Q : Matrix n n ℤ) (hd : B.det ≠ 0)
    (h : P * B = B * Q) : Q * B.adjugate = B.adjugate * P := by
  have h1 : B.adjugate * (P * B) * B.adjugate = B.adjugate * (B * Q) * B.adjugate := by rw [h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ B, mul_adjugate, adjugate_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact (smul_right_injective _ hd h1).symm
end GlobalTheory
