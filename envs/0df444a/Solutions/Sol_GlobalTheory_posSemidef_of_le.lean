-- Prove2me | solution 1 for GlobalTheory.posSemidef_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:46.772091+00:00
-- url     : https://prove2.me/submissions/7e9360e7-622d-4944-9e01-1b960b9b00a2

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
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef :=
  (hA.nonneg.trans h).posSemidef
end GlobalTheory
