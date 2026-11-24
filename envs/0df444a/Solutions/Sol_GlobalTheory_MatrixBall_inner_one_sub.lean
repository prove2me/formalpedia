-- Prove2me | solution 1 for GlobalTheory.MatrixBall.inner_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:24.970331+00:00
-- url     : https://prove2.me/submissions/e4daae00-e58f-4c40-807f-b2a75c054e2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
import Theorems.Thm_GlobalTheory_MatrixBall_inner_conjTranspose_mul

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
theorem _root_.solution (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (1 - Mᴴ * M) x⟫_ℂ = ((‖x‖ ^ 2 - ‖toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, inner_conjTranspose_mul, toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
end GlobalTheory.MatrixBall
