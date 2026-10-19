-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.approximation_center_exp_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T09:07:40.213567+00:00
-- url     : https://prove2.me/submissions/8473e1cc-b1a9-4879-a1ad-225c3f3528d9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (p : ℤ) (q j K : ℕ) (nu : ℝ)
    (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu) (hq : 1 ≤ q)
    (happrox : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) *
      (2 * Complex.I * (p : ℂ) / (q : ℂ) -
        2 * Complex.I * (Real.pi : ℂ))‖ ≤
      Real.exp (Real.log (2 * (K : ℝ)) + nu -
        nu * (⌈Real.log (q : ℝ)⌉₊ : ℝ)) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : 0 < 2 * (K : ℝ) := by linarith
  have hjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  -- The imaginary unit is retained in the algebraic identity.
  have hform :
      (j : ℂ) *
        (2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * Complex.I * (Real.pi : ℂ)) =
        ((2 * (j : ℝ) * ((p : ℝ) / q - Real.pi) : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.ofReal_intCast]
    ring
  have hnorm :
      ‖(j : ℂ) *
        (2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * Complex.I * (Real.pi : ℂ))‖ =
        2 * (j : ℝ) * |(p : ℝ) / q - Real.pi| := by
    rw [hform]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_mul, abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hj0]
  have happrox' : |(p : ℝ) / q - Real.pi| ≤ (q : ℝ) ^ (-nu) := by
    simpa only [abs_sub_comm] using happrox
  have hleft :
      2 * (j : ℝ) * |(p : ℝ) / q - Real.pi| ≤
        (2 * (K : ℝ)) * (q : ℝ) ^ (-nu) := by
    calc
      2 * (j : ℝ) * |(p : ℝ) / q - Real.pi| ≤
          (2 * (K : ℝ)) * |(p : ℝ) / q - Real.pi| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hjR (by norm_num)) (abs_nonneg _)
      _ ≤ (2 * (K : ℝ)) * (q : ℝ) ^ (-nu) :=
        mul_le_mul_of_nonneg_left happrox' hKpos.le
  have hceil :
      (⌈Real.log (q : ℝ)⌉₊ : ℝ) < Real.log (q : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.log_nonneg hqR)
  have harg :
      Real.log (2 * (K : ℝ)) - nu * Real.log (q : ℝ) ≤
        Real.log (2 * (K : ℝ)) + nu -
          nu * (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hceil.le hnu
    nlinarith only [hmul]
  have hbase :
      (2 * (K : ℝ)) * (q : ℝ) ^ (-nu) =
        Real.exp (Real.log (2 * (K : ℝ)) - nu * Real.log (q : ℝ)) := by
    calc
      (2 * (K : ℝ)) * (q : ℝ) ^ (-nu) =
          Real.exp (Real.log (2 * (K : ℝ))) *
            Real.exp (Real.log (q : ℝ) * (-nu)) := by
        rw [Real.exp_log hKpos, Real.rpow_def_of_pos hqpos]
      _ = Real.exp (Real.log (2 * (K : ℝ)) - nu * Real.log (q : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    ‖(j : ℂ) *
        (2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * Complex.I * (Real.pi : ℂ))‖ =
        2 * (j : ℝ) * |(p : ℝ) / q - Real.pi| := hnorm
    _ ≤ (2 * (K : ℝ)) * (q : ℝ) ^ (-nu) := hleft
    _ = Real.exp (Real.log (2 * (K : ℝ)) - nu * Real.log (q : ℝ)) := hbase
    _ ≤ Real.exp (Real.log (2 * (K : ℝ)) + nu -
          nu * (⌈Real.log (q : ℝ)⌉₊ : ℝ)) :=
      Real.exp_le_exp.mpr harg