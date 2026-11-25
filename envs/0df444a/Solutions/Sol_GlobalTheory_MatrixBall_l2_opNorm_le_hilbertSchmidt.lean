-- Prove2me | solution 1 for GlobalTheory.MatrixBall.l2_opNorm_le_hilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:23.095441+00:00
-- url     : https://prove2.me/submissions/efae5683-0d04-4f03-8a77-e8c77dc2f7af

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
omit [DecidableEq m]
namespace GlobalTheory.MatrixBall
theorem _root_.solution (Z : Matrix m n ℂ) :
    ‖Z‖ ≤ Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, Z i j * x j‖ ≤ ∑ j, ‖Z i j‖ * ‖x j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  calc _ = ‖∑ j, Z i j * x j‖ ^ 2 := rfl
    _ ≤ (∑ j, ‖Z i j‖ * ‖x j‖) ^ 2 := by gcongr
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end GlobalTheory.MatrixBall
