-- Prove2me | solution 1 for GlobalTheory.MatrixBall.inner_conjTranspose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:54:32.535092+00:00
-- url     : https://prove2.me/submissions/016ae79a-fd61-4a65-b04f-7f0c7bc409c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
open GlobalTheory
open GlobalTheory.MatrixBall
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace GlobalTheory.MatrixBall
theorem _root_.solution (M N : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (Mᴴ * N) y⟫_ℂ = ⟪toEuclideanLin M x, toEuclideanLin N y⟫_ℂ := by
  rw [toLpLin_mul (q := 2), LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]
end GlobalTheory.MatrixBall
