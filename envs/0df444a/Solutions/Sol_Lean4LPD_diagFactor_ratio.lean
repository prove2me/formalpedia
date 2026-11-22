-- Prove2me | solution 1 for Lean4LPD.diagFactor_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:58.212832+00:00
-- url     : https://prove2.me/submissions/e8818029-810d-497c-95f9-8ed185de0469

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Theorems.Thm_Lean4LPD_exp_four_thirds_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} (hj : 2 ≤ j) : diagFactor (j + 1) ≤ 9 / 4 * diagFactor j := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpos : (0 : ℝ) < 2 * (j : ℝ) - 1 := by linarith
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  -- ((2j+1)/(2j-1))^j = (1 + 2/(2j-1))^j <= exp(2j/(2j-1)) <= exp(4/3)
  have hratio : ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j ≤ 4.03 := by
    have hbase : (2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1) ≤ Real.exp (2 / (2 * (j : ℝ) - 1)) := by
      have h := Real.add_one_le_exp (2 / (2 * (j : ℝ) - 1))
      rw [div_le_iff₀ hpos]
      have hd : 2 / (2 * (j : ℝ) - 1) * (2 * (j : ℝ) - 1) = 2 := by field_simp
      nlinarith [h, Real.exp_pos (2 / (2 * (j : ℝ) - 1)), hd]
    have hb0 : (0 : ℝ) ≤ (2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1) := by positivity
    have hpow : ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
        ≤ Real.exp (2 / (2 * (j : ℝ) - 1)) ^ j := pow_le_pow_left₀ hb0 hbase j
    have hexp : Real.exp (2 / (2 * (j : ℝ) - 1)) ^ j
        = Real.exp ((j : ℝ) * (2 / (2 * (j : ℝ) - 1))) := (Real.exp_nat_mul _ j).symm
    have harg : (j : ℝ) * (2 / (2 * (j : ℝ) - 1)) ≤ 4 / 3 := by
      have hre : (j : ℝ) * (2 / (2 * (j : ℝ) - 1)) = 2 * (j : ℝ) / (2 * (j : ℝ) - 1) := by ring
      rw [hre, div_le_iff₀ hpos]
      linarith [hj2]
    calc ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
        ≤ Real.exp (2 / (2 * (j : ℝ) - 1)) ^ j := hpow
      _ = Real.exp ((j : ℝ) * (2 / (2 * (j : ℝ) - 1))) := hexp
      _ ≤ Real.exp (4 / 3) := Real.exp_le_exp.mpr harg
      _ ≤ 4.03 := exp_four_thirds_le
  -- assemble
  have hnum : (2 * ((j : ℝ) + 1) - 1) ^ (j + 1)
      = (2 * (j : ℝ) + 1) * ((2 * (j : ℝ) - 1) ^ j
          * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j) := by
    rw [div_pow, ← mul_div_assoc, mul_comm ((2 * (j:ℝ) - 1) ^ j), mul_div_assoc,
      div_self (by positivity), mul_one]
    have : (2 * ((j : ℝ) + 1) - 1) = 2 * (j : ℝ) + 1 := by ring
    rw [this, pow_succ]
    ring
  have hfacsucc : (Nat.factorial (j + 1) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hcast : ((j : ℕ) : ℝ) + 1 = (((j + 1 : ℕ)) : ℝ) := by push_cast; ring
  have hp : (0 : ℝ) < (2 * (j : ℝ) - 1) ^ j := pow_pos hpos j
  unfold diagFactor
  rw [hfacsucc, ← hcast, hnum]
  have hrhs : 9 / 4 * ((2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)))
      = (9 / 4 * (2 * (j : ℝ) - 1) ^ j) / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by
    ring
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hquad : (2 * (j : ℝ) + 1) * 4.03 ≤ 9 / 4 * ((j : ℝ) + 1) ^ 2 := by
    nlinarith [hj2, sq_nonneg ((j : ℝ) - 2)]
  have hkey : (2 * (j : ℝ) + 1) * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
      ≤ 9 / 4 * ((j : ℝ) + 1) ^ 2 := by
    have h1 : (2 * (j : ℝ) + 1) * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
        ≤ (2 * (j : ℝ) + 1) * 4.03 := mul_le_mul_of_nonneg_left hratio (by linarith)
    linarith [hquad]
  have hBF : (0 : ℝ) < (2 * (j : ℝ) - 1) ^ j
      * ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt hBF)]
end Lean4LPD
