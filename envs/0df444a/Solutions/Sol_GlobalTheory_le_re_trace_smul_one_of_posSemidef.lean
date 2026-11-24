-- Prove2me | solution 1 for GlobalTheory.le_re_trace_smul_one_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:46.708572+00:00
-- url     : https://prove2.me/submissions/5217ce6f-e191-41fb-b699-022bc8dbb3a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_le_trace_smul_one_of_posSemidef
import Theorems.Thm_GlobalTheory_smul_eq_re_smul_of_nonneg

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
theorem _root_.solution {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ RCLike.re A.trace • (1 : Matrix n n 𝕜) := by
  rw [← smul_eq_re_smul_of_nonneg hA.trace_nonneg]
  exact le_trace_smul_one_of_posSemidef hA
end GlobalTheory
