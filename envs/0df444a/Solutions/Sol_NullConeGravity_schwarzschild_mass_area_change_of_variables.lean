-- Prove2me | solution 1 for NullConeGravity.schwarzschild_mass_area_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:15:09.189805+00:00
-- url     : https://prove2.me/submissions/e0d12f4c-d7d7-4cae-aa56-0627cfcc6319

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Set

theorem solution
    (c a b : ℝ) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ s in c * a ^ 2..c * b ^ 2, F s / Real.sqrt s) =
      2 * Real.sqrt c * ∫ m in a..b, F (c * m ^ 2) := by
  have hm {m : ℝ} (h : m ∈ uIcc a b) : 0 < m :=
    lt_of_lt_of_le ha ((uIcc_of_le hab) ▸ h).1
  have hd (m : ℝ) : HasDerivAt (fun x : ℝ => c * x ^ 2) (c * (2 * m)) m := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hasDerivAt_pow 2 m).const_mul c
  have hden : ContinuousOn (fun s : ℝ => F s / Real.sqrt s)
      ((fun m : ℝ => c * m ^ 2) '' uIcc a b) := by
    apply hF.continuousOn.div Real.continuous_sqrt.continuousOn
    rintro y ⟨m, h, rfl⟩
    exact (Real.sqrt_pos.2 (mul_pos hc (pow_pos (hm h) 2))).ne'
  have hs := intervalIntegral.integral_comp_mul_deriv'
    (fun m _ => hd m) (continuous_const.mul (continuous_const.mul continuous_id)).continuousOn hden
  calc
    _ = ∫ m in a..b, (F (c * m ^ 2) / Real.sqrt (c * m ^ 2)) * (c * (2 * m)) := hs.symm
    _ = ∫ m in a..b, 2 * Real.sqrt c * F (c * m ^ 2) := by
      apply intervalIntegral.integral_congr
      intro m h
      change F (c * m ^ 2) / Real.sqrt (c * m ^ 2) * (c * (2 * m)) = 2 * Real.sqrt c * F (c * m ^ 2)
      rw [Real.sqrt_mul hc.le, Real.sqrt_sq (hm h).le, div_mul_eq_mul_div]
      apply (div_eq_iff (mul_ne_zero (Real.sqrt_pos.2 hc).ne' (hm h).ne')).2
      calc
        _ = F (c * m ^ 2) * ((Real.sqrt c) ^ 2 * (2 * m)) := by rw [Real.sq_sqrt hc.le]
        _ = _ := by ring
    _ = _ := intervalIntegral.integral_const_mul _ _
