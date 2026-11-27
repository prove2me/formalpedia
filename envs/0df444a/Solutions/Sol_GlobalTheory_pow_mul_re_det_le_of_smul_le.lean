-- Prove2me | solution 1 for GlobalTheory.pow_mul_re_det_le_of_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:51.859842+00:00
-- url     : https://prove2.me/submissions/a330d177-a795-41a3-ac6a-d6a02253e831

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_re_det_le_re_det_of_posSemidef_of_le

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
theorem _root_.solution {B B' : Matrix n n 𝕜} (hB : B.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) (h : c • B ≤ B') :
    c ^ Fintype.card n * RCLike.re B.det ≤ RCLike.re B'.det := by
  have := re_det_le_re_det_of_posSemidef_of_le (hB.smul hc) h
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul] at this
end GlobalTheory
