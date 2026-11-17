-- Prove2me | solution 1 for N25.siegelFun_first_index_shift
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:48.876998+00:00
-- url     : https://prove2.me/submissions/24048033-459d-4cab-9f1e-5de47d77d929

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level

set_option autoImplicit false

namespace N25

theorem _root_.solution (N : ℕ) (r s k : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N (r + k * (N : ℤ)) s (τ : ℂ) =
      (-Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ)))) ^ k *
        ModularCurve.siegelFun N r s (τ : ℂ) := by
  let c := -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ)))
  have hc : c ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
  have hpow (j : ℤ) : c * c ^ j = c ^ (j + 1) := by
    rw [zpow_add₀ hc, zpow_one]
    ring
  change ModularCurve.siegelFun N (r + k * (N : ℤ)) s (τ : ℂ) =
    c ^ k * ModularCurve.siegelFun N r s (τ : ℂ)
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show r + ((n : ℤ) + 1) * (N : ℤ) = (r + (n : ℤ) * N) + N by ring,
      (ModularCurve.SiegelUnit.siegelFun_add_level N (r + (n : ℤ) * N) s).2 τ, ih]
    change c * (c ^ (n : ℤ) * _) = _
    rw [← mul_assoc, hpow]
  | pred n ih =>
    have hs := (ModularCurve.SiegelUnit.siegelFun_add_level N
      (r + (-(n : ℤ) - 1) * N) s).2 τ
    rw [show r + (-(n : ℤ) - 1) * N + N = r + (-(n : ℤ)) * N by ring] at hs
    apply mul_left_cancel₀ hc
    rw [← hs, ih, ← mul_assoc, hpow]
    congr 1
    congr 1
    ring

end N25
