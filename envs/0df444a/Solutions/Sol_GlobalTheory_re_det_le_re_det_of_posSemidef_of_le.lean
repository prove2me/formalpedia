-- Prove2me | solution 1 for GlobalTheory.re_det_le_re_det_of_posSemidef_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:36.451569+00:00
-- url     : https://prove2.me/submissions/074f4f1d-57df-442b-8c73-eb00b98b7635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_det_le_det_of_posSemidef_of_le

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
variable [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det :=
  (RCLike.le_iff_re_im.mp (det_le_det_of_posSemidef_of_le hA h)).1
end GlobalTheory
