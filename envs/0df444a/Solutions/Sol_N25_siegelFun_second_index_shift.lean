-- Prove2me | solution 1 for N25.siegelFun_second_index_shift
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:22.336205+00:00
-- url     : https://prove2.me/submissions/5eba4599-c22f-423b-af79-9335046e5f85

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level

set_option autoImplicit false

namespace N25

/-- The second Siegel index may be shifted by any integer multiple of its
level, with the exact exponential multiplier retained. -/
theorem _root_.solution (N : ℕ) (r s k : ℤ) (z : ℂ) :
    ModularCurve.siegelFun N r (s + k * (N : ℤ)) z =
      Complex.exp (Real.pi * Complex.I * (k : ℂ) *
        ((r : ℂ) - (N : ℂ)) / (N : ℂ)) *
      ModularCurve.siegelFun N r s z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show s + ((n : ℤ) + 1) * (N : ℤ) = (s + (n : ℤ) * N) + N by ring]
    rw [(ModularCurve.SiegelUnit.siegelFun_add_level N r (s + (n : ℤ) * N)).1 z, ih]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  | pred n ih =>
    have hs := (ModularCurve.SiegelUnit.siegelFun_add_level N r
      (s + (-(n : ℤ) - 1) * N)).1 z
    rw [show s + (-(n : ℤ) - 1) * N + N = s + (-(n : ℤ)) * N by ring] at hs
    apply (mul_left_cancel₀ (Complex.exp_ne_zero
      (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ))))
    rw [← hs, ih, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end N25
