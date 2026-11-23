-- Prove2me | solution 1 for GlobalTheory.polar_realExt_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:06.01174+00:00
-- url     : https://prove2.me/submissions/751396bf-c2a4-4dec-83a8-d469d480f2be

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
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) (x y : X) :
    QuadraticMap.polar (realExt Q) (1 ⊗ₜ x) (1 ⊗ₜ y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← tmul_add, realExt_tmul, one_mul]
end GlobalTheory
