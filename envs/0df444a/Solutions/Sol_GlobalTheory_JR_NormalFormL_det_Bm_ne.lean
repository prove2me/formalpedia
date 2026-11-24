-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.det_Bm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:06:02.388124+00:00
-- url     : https://prove2.me/submissions/321cfcaa-5e5a-431a-ac1b-2027975f2598

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_hankel_eq

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
theorem _root_.solution (Y : Gl r k) (h : Delta (inv Y) ≠ 0) : (Bm Y).det ≠ 0 := by
  intro h0
  apply h
  rw [Delta, ← hankel_eq, det_mul, h0, mul_zero]
end GlobalTheory.JR.NormalFormL
