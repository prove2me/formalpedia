-- Prove2me | solution 1 for GlobalTheory.eq_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:58.829798+00:00
-- url     : https://prove2.me/submissions/c8d0eb24-957a-4c2b-8a76-1034fc7d6695

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
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) (P : QuadraticForm ℝ (ℝ ⊗[ℤ] X))
    (h : ∀ x, P (1 ⊗ₜ x) = Q x) : P = realExt Q := by
  apply QuadraticMap.polarBilin_injective (R := ℝ) (IsUnit.mk0 2 two_ne_zero)
  ext x y
  simp [QuadraticMap.polar, ← tmul_add, h]
end GlobalTheory
