-- Prove2me | solution 1 for GlobalTheory.realExt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:23.332918+00:00
-- url     : https://prove2.me/submissions/3d256960-39a6-4782-998e-18a41f455caf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
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
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) (v : ℝ ⊗[ℤ] X) :
    realExt Q v = realExtBilin Q.polarBilin v v / 2 := by
  simp only [realExt, QuadraticMap.smul_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    smul_eq_mul]
  ring
end GlobalTheory
