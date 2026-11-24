-- Prove2me | solution 1 for GlobalTheory.re_trace_mul_nonneg_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:41.47558+00:00
-- url     : https://prove2.me/submissions/3d37c3cc-98f8-4c4e-8649-d85b702f0ce4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_trace_mul_nonneg_of_posSemidef

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
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1
end GlobalTheory
