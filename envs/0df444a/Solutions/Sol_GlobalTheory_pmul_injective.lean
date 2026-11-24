-- Prove2me | solution 1 for GlobalTheory.pmul_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:13.583836+00:00
-- url     : https://prove2.me/submissions/bacfcfb3-fd55-480a-b94d-dd162ced9254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) (h : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Function.Injective (ConcreteCategory.hom ((p : ℤ) • 𝟙 M)) := by
  intro a b hab
  have hab' : (p : ℤ) • a = (p : ℤ) • b := hab
  apply sub_eq_zero.mp
  apply h
  rw [zsmul_sub, hab', sub_self]
end GlobalTheory
