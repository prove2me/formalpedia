-- Prove2me | solution 1 for GlobalTheory.ExpPow.exp_I_pow_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:23.035198+00:00
-- url     : https://prove2.me/submissions/44be5fec-4a44-485c-ade0-ceddc76c16e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PowExpIOrInvInjective
import Theorems.Thm_GlobalTheory_ExpPow_int_eq_zero_of_exp_I_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExpPow
namespace GlobalTheory.ExpPow
theorem _root_.solution (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul] at h
  have h2 : Complex.exp (Complex.I * (((a : ℤ) - b : ℤ) : ℂ)) = 1 := by
    have : Complex.I * (((a : ℤ) - b : ℤ) : ℂ) = a * Complex.I - b * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  have := int_eq_zero_of_exp_I_mul _ h2
  omega
end GlobalTheory.ExpPow
