-- Prove2me | solution 1 for Lean4LPD.epsJump_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:09.741901+00:00
-- url     : https://prove2.me/submissions/74d3dce4-bcfc-47b2-862a-025c587d3fff

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Theorems.Thm_Lean4LPD_one_add_inv_pow_le_exp_one

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {j nu : ℕ} (hnu : 1 ≤ nu) (hj : nu ≤ j) :
    epsJump kh1 c a (j + 1) nu ≤ betaOf kh1 c a * epsJump kh1 c a j nu := by
  have hj1 : 1 ≤ j := le_trans hnu hj
  have hnuR : (1 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hnujR : (nu : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  set W := rungW kh1 c (nu + j) with hWdef
  set W' := rungW kh1 c (nu + j + 1) with hW'def
  set w2 := rungW kh1 c 2 with hw2def
  have hcast1 : ((nu + j : ℕ) : ℝ) = (nu : ℝ) + (j : ℝ) := by push_cast; ring
  have hcast2 : ((nu + j + 1 : ℕ) : ℝ) = (nu : ℝ) + (j : ℝ) + 1 := by push_cast; ring
  have hWval : W = kh1 * ((nu : ℝ) + (j : ℝ) - 1 + c) := by
    rw [hWdef]; unfold rungW; rw [hcast1]
  have hW'val : W' = kh1 * ((nu : ℝ) + (j : ℝ) + c) := by
    rw [hW'def]; unfold rungW; rw [hcast2]; ring_nf
  have hw2val : w2 = kh1 * (1 + c) := by
    rw [hw2def]; unfold rungW; norm_num
  have hWpos : 0 < W := by
    rw [hWval]
    have : (1 : ℝ) ≤ (nu : ℝ) + (j : ℝ) - 1 + c := by linarith
    have h2 : (0 : ℝ) < (nu : ℝ) + (j : ℝ) - 1 + c := by linarith
    positivity
  have hW'nonneg : 0 ≤ W' := by
    rw [hW'val]
    have : (0 : ℝ) ≤ (nu : ℝ) + (j : ℝ) + c := by linarith
    positivity
  -- estimate 1: W' ≤ W * (1 + 1/j)
  have hest1 : W' ≤ W * (1 + 1 / (j : ℝ)) := by
    rw [hWval, hW'val]
    have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
    have hkey : (nu : ℝ) + (j : ℝ) + c
        ≤ ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 + 1 / (j : ℝ)) := by
      have hd : (1 : ℝ) ≤ ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 / (j : ℝ)) := by
        rw [mul_one_div, le_div_iff₀ hjpos]
        linarith [hnuR, hc]
      have hexpand : ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 + 1 / (j : ℝ))
          = ((nu : ℝ) + (j : ℝ) - 1 + c) + ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 / (j : ℝ)) := by
        ring
      rw [hexpand]
      linarith [hd]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hkey hkh.le
  -- estimate 2: W' ≤ 2 * w2 * j
  have hest2 : W' ≤ 2 * w2 * (j : ℝ) := by
    rw [hW'val, hw2val]
    have h1 : (nu : ℝ) + (j : ℝ) + c ≤ (1 + c) * (2 * (j : ℝ)) := by
      nlinarith only [hnujR, hjR, hc]
    calc
      _ ≤ kh1 * ((1 + c) * (2 * (j : ℝ))) := mul_le_mul_of_nonneg_left h1 hkh.le
      _ = _ := by ring
  -- assemble
  have hfacj : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfacj1 : (Nat.factorial (j + 1) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpowj : (W' * a) ^ j ≤ (W * (1 + 1 / (j : ℝ)) * a) ^ j :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hest1 ha) j
  have hsplit : (W * (1 + 1 / (j : ℝ)) * a) ^ j = (W * a) ^ j * (1 + 1 / (j : ℝ)) ^ j := by
    rw [show W * (1 + 1 / (j : ℝ)) * a = (W * a) * (1 + 1 / (j : ℝ)) by ring, mul_pow]
  have hexp := one_add_inv_pow_le_exp_one hj1
  have hWa : (0 : ℝ) ≤ (W * a) ^ j := by positivity
  have hchain : (W' * a) ^ j ≤ (W * a) ^ j * Real.exp 1 := by
    calc (W' * a) ^ j ≤ (W * (1 + 1 / (j : ℝ)) * a) ^ j := hpowj
      _ = (W * a) ^ j * (1 + 1 / (j : ℝ)) ^ j := hsplit
      _ ≤ (W * a) ^ j * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_left hexp hWa
  -- (W'a)^{j+1} = (W'a)^j * (W'a) <= (Wa)^j * e * 2 w2 a * (j+1)
  have hlast : (W' * a) ^ (j + 1) ≤ (W * a) ^ j * Real.exp 1 * (2 * w2 * a) * ((j : ℝ) + 1) := by
    have hW'a : (0 : ℝ) ≤ W' * a := by positivity
    have h1 : W' * a ≤ 2 * w2 * a * (j : ℝ) := by
      calc
        _ ≤ (2 * w2 * (j : ℝ)) * a := mul_le_mul_of_nonneg_right hest2 ha
        _ = _ := by ring
    have h2 : (W' * a) ^ (j + 1) = (W' * a) ^ j * (W' * a) := by rw [pow_succ]
    have hep : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
    have hw2a : (0 : ℝ) ≤ 2 * w2 * a := by
      have : 0 ≤ w2 := by rw [hw2val]; positivity
      positivity
    calc (W' * a) ^ (j + 1) = (W' * a) ^ j * (W' * a) := h2
      _ ≤ ((W * a) ^ j * Real.exp 1) * (2 * w2 * a * (j : ℝ)) := by
          apply mul_le_mul hchain h1 hW'a (by positivity)
      _ ≤ (W * a) ^ j * Real.exp 1 * (2 * w2 * a) * ((j : ℝ) + 1) := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num))
              (mul_nonneg (mul_nonneg hWa hep) hw2a)
  -- convert to the statement
  have hnucast : nu + (j + 1) = nu + j + 1 := by omega
  unfold epsJump betaOf
  rw [hnucast, ← hW'def, ← hWdef, ← hw2def, hfacj1]
  have hrhs : 2 * Real.exp 1 * w2 * a * ((W * a) ^ j / (Nat.factorial j : ℝ))
      = (2 * Real.exp 1 * w2 * a * (W * a) ^ j) / (Nat.factorial j : ℝ) := by ring
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right hlast hfacj.le]
end Lean4LPD
