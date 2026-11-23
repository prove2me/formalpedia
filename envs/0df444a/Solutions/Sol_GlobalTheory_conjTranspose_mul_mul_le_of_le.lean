-- Prove2me | solution 1 for GlobalTheory.conjTranspose_mul_mul_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:18.621961+00:00
-- url     : https://prove2.me/submissions/227dcd41-d14d-462c-970c-a0e7b2f68ac6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open GlobalTheory
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
namespace GlobalTheory
theorem _root_.solution {m : Type*} [Finite m] {A B : Matrix n n 𝕜} (h : A ≤ B)
    (C : Matrix n m 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  have := (le_iff.mp h).conjTranspose_mul_mul_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this
end GlobalTheory
