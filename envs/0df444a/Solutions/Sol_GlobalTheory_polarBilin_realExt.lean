-- Prove2me | solution 1 for GlobalTheory.polarBilin_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:41.822628+00:00
-- url     : https://prove2.me/submissions/d8027726-0301-4d98-9ff2-fbea980fbe91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_GlobalTheory_polar_realExt_one_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) :
    (realExt Q).polarBilin = realExtBilin Q.polarBilin := by
  ext x y
  simp [polar_realExt_one_tmul]
end GlobalTheory
