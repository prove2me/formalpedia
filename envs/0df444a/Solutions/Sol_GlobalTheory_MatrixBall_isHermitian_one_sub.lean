-- Prove2me | solution 1 for GlobalTheory.MatrixBall.isHermitian_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:54:34.008326+00:00
-- url     : https://prove2.me/submissions/b43cb796-22f3-452b-bbab-4bfb0ad7ee42

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
omit [DecidableEq n]
namespace GlobalTheory.MatrixBall
theorem _root_.solution [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self M)
end GlobalTheory.MatrixBall
