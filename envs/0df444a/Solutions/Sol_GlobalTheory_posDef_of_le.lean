-- Prove2me | solution 1 for GlobalTheory.posDef_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:43.748535+00:00
-- url     : https://prove2.me/submissions/a6e38d3f-61cb-433a-9651-e1ade2e5cdf1

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
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) : B.PosDef := by
  have := hA.add_posSemidef (le_iff.mp h)
  rwa [add_sub_cancel] at this
end GlobalTheory
