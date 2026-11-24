-- Prove2me | solution 1 for GlobalTheory.MatrixBall.norm_toEuclideanLin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:54:35.055706+00:00
-- url     : https://prove2.me/submissions/7ae92a65-d9e1-40a5-8ad7-43c52b4e35f4

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
theorem _root_.solution (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  M.l2_opNorm_mulVec x
end GlobalTheory.MatrixBall
