-- Prove2me | solution 1 for GlobalTheory.transpose_le_transpose_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:37:49.287516+00:00
-- url     : https://prove2.me/submissions/3b4165a8-c16f-4f4b-897e-2f45240aadb0

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
omit [Fintype n]
namespace GlobalTheory
theorem _root_.solution {A B : Matrix n n 𝕜} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  have := (le_iff.mp h).transpose
  rwa [transpose_sub] at this
end GlobalTheory
