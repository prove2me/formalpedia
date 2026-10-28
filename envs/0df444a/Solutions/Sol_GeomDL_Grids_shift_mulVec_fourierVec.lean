-- Prove2me | solution 1 for GeomDL.Grids.shift_mulVec_fourierVec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:50:14.108129+00:00
-- url     : https://prove2.me/submissions/b02b76cd-1bed-4d9f-a11f-8213f4d0a0eb

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix GeomDL.Grids

theorem e_mod_aux (n : ℕ) (hn : 0 < n) (k a : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k * a : ℕ) : ℂ) / (n : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k * (a % n) : ℕ) : ℂ) / (n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : k * a = k * (a % n) + n * (k * (a / n)) := by
    conv_lhs => rw [← Nat.mod_add_div a n]
    ring
  rw [ha]
  have : 2 * (Real.pi : ℂ) * Complex.I * ((k * (a % n) + n * (k * (a / n)) : ℕ) : ℂ) / (n : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * ((k * (a % n) : ℕ) : ℂ) / (n : ℂ) +
        ((k * (a / n) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem solution {n : ℕ} [NeZero n] (k : ZMod n) :
    shift ℂ n *ᵥ fourierVec n k =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) • fourierVec n k ∧
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) ^ n = 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · funext u
    have hs : (shift ℂ n *ᵥ fourierVec n k) u = fourierVec n k (u - 1) := by
      simp only [mulVec, dotProduct, shift, circulant_apply]
      rw [Finset.sum_eq_single (u - 1)]
      · simp
      · intro v _ hv
        have : u - v ≠ 1 := by
          intro h; apply hv; rw [← h]; ring
        simp [Pi.single_apply, this]
      · simp
    rw [hs, Pi.smul_apply, smul_eq_mul]
    simp only [fourierVec]
    have hu : u.val = ((u - 1).val + 1) % n := by
      have h1 : u = (u - 1) + 1 := by ring
      conv_lhs => rw [h1]
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have key := e_mod_aux n hn k.val ((u - 1).val + 1)
    rw [← hu] at key
    rw [← key]
    have : 2 * (Real.pi : ℂ) * Complex.I * ((k.val * ((u - 1).val + 1) : ℕ) : ℂ) / (n : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * ((k.val * (u - 1).val : ℕ) : ℂ) / (n : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ) := by
      push_cast; ring
    rw [this, Complex.exp_add]
    have hB : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ)) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination (-(((Real.sqrt n : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k.val * (u - 1).val : ℕ) : ℂ) / (n : ℂ)))) * hB
  · rw [← Complex.exp_nat_mul]
    have : (n : ℂ) * -(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ)) =
        -((k.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      field_simp
    rw [this, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]
