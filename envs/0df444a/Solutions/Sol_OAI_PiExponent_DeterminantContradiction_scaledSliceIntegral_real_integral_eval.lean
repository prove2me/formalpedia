-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_real_integral_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:28:00.666549+00:00
-- url     : https://prove2.me/submissions/754adf3b-7b6a-42d5-ad91-4176e46281ef

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then (1 - t) ^ n else 0)
      ∂MeasureTheory.volume = (((n : ℝ) + 1)⁻¹) := by
  have hfun :
      (fun t : ℝ => if 0 ≤ t ∧ t ≤ 1 then (1 - t) ^ n else 0) =
        (Set.Icc (0 : ℝ) 1).indicator (fun t => (1 - t) ^ n) := by
    funext t
    by_cases ht : 0 ≤ t ∧ t ≤ 1 <;> simp [Set.indicator, Set.mem_Icc, ht]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from zero_le_one)]
  let F : ℝ → ℝ := fun x => -(((n : ℝ) + 1)⁻¹) * (1 - x) ^ (n + 1)
  have hn : (n : ℝ) + 1 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F ((1 - x) ^ n) x := by
    intro x hx
    have hb : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa only [id_eq] using (hasDerivAt_id x).const_sub 1
    have hh : HasDerivAt F
        (-(((n : ℝ) + 1)⁻¹) *
          (((n + 1 : ℕ) : ℝ) * (1 - x) ^ (n + 1 - 1) * (-1))) x :=
      (hb.fun_pow (n + 1)).const_mul (-(((n : ℝ) + 1)⁻¹))
    have hscalar :
        -(((n : ℝ) + 1)⁻¹) *
          (((n + 1 : ℕ) : ℝ) * (1 - x) ^ (n + 1 - 1) * (-1)) =
          (1 - x) ^ n := by
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      calc
        -(((n : ℝ) + 1)⁻¹) * (((n : ℝ) + 1) * (1 - x) ^ n * (-1)) =
            (((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)) * (1 - x) ^ n := by ring
        _ = (1 - x) ^ n := by rw [inv_mul_cancel₀ hn, one_mul]
    rw [hscalar] at hh
    exact hh
  have hcont : Continuous (fun x : ℝ => (1 - x) ^ n) :=
    (continuous_const.sub continuous_id).pow n
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)]
  simp [F]