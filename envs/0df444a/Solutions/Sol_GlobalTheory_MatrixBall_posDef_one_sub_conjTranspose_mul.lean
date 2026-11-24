-- Prove2me | solution 1 for GlobalTheory.MatrixBall.posDef_one_sub_conjTranspose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:21.01192+00:00
-- url     : https://prove2.me/submissions/4183836f-0346-4d11-8b30-bb6a2f1337be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
import Theorems.Thm_GlobalTheory_MatrixBall_norm_toEuclideanLin_le
import Theorems.Thm_GlobalTheory_MatrixBall_dotProduct_mulVec_eq_inner
import Theorems.Thm_GlobalTheory_MatrixBall_inner_one_sub
import Theorems.Thm_GlobalTheory_MatrixBall_isHermitian_one_sub

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
theorem _root_.solution {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_one_sub Z) fun v hv => ?_
  rw [dotProduct_mulVec_eq_inner, inner_one_sub]
  have hx : 0 < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by
    rw [norm_pos_iff]; intro h; exact hv (by simpa using h)
  have h1 := norm_toEuclideanLin_le Z (toLp 2 v)
  have h2 : ‖toEuclideanLin Z (toLp 2 v)‖ < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by nlinarith
  have h3 := norm_nonneg (toEuclideanLin Z (toLp 2 v))
  exact_mod_cast (by nlinarith : (0 : ℝ) < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 -
    ‖toEuclideanLin Z (toLp 2 v)‖ ^ 2)
end GlobalTheory.MatrixBall
