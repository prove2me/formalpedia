-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.hankel_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:59.297817+00:00
-- url     : https://prove2.me/submissions/9657328e-7bbd-4615-8259-42945867c09b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_mom_sec_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (Y : Gl r k) : Cm Y * Bm Y = hankel (inv Y) := by
  ext i j
  simp only [mul_apply, Cm, Bm, hankel, of_apply, mom_sec_inv]
  simp only [mom]
  rw [pow_add, ← mulVec_mulVec, dotProduct_mulVec]
  rfl
end GlobalTheory.JR.NormalFormL
