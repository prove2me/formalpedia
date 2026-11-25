-- Prove2me | solution 1 for GlobalTheory.MatrixBall.posDef_iff_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:27.455811+00:00
-- url     : https://prove2.me/submissions/525c3680-3d35-46a2-b019-493e61c7fe6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
import Theorems.Thm_GlobalTheory_MatrixBall_posDef_one_sub_conjTranspose_mul
import Theorems.Thm_GlobalTheory_MatrixBall_norm_lt_one_of_posDef

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
theorem _root_.solution (Z : Matrix m n ℂ) : (1 - Zᴴ * Z).PosDef ↔ ‖Z‖ < 1 :=
  ⟨norm_lt_one_of_posDef, posDef_one_sub_conjTranspose_mul⟩
end GlobalTheory.MatrixBall
