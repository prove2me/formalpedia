-- Prove2me | solution 1 for GeomDL.Grids.fourierMatrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:51:16.706392+00:00
-- url     : https://prove2.me/submissions/8200430b-91d7-4b1d-b8b1-92ae3e619905

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs
open Complex Matrix

theorem eq_of_exp_aux {n : ℕ} (hn : 0 < n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (n : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (n : ℂ))) : a = b := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp at hm
  have k2 : ((a : ℤ) : ℂ) = ((b + m * n : ℤ) : ℂ) := by
    push_cast
    linear_combination hm
  have k3 : (a : ℤ) = b + m * n := by exact_mod_cast k2
  have : m = 0 := by
    rcases lt_trichotomy m 0 with h1 | h1 | h1
    · have : m * (n:ℤ) ≤ -n := by nlinarith
      omega
    · exact h1
    · have : (n:ℤ) ≤ m * n := by nlinarith
      omega
  subst this
  omega

open GeomDL.Grids

theorem solution {n : ℕ} [NeZero n] :
    (fourierMatrix n)ᴴ * fourierMatrix n = 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  ext k l
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l.val : ℂ) - k.val) / (n : ℂ)) with hζ
  have hc : ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  have term : ∀ u : ZMod n, star (fourierVec n k u) * fourierVec n l u = (n : ℂ)⁻¹ * ζ ^ u.val := by
    intro u
    simp only [fourierVec, hζ, star_mul', ← Complex.exp_conj, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, map_mul, map_div₀, Complex.conj_I, Complex.conj_natCast, map_ofNat]
    rw [← Complex.exp_nat_mul]
    calc _ = (((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
          (Complex.exp (2 * (Real.pi : ℂ) * -Complex.I * ((k.val * u.val : ℕ) : ℂ) / (n : ℂ)) *
           Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l.val * u.val : ℕ) : ℂ) / (n : ℂ))) := by ring
      _ = _ := by
        rw [hc, ← Complex.exp_add]
        congr 2
        push_cast; ring
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, fourierMatrix]
  rw [Finset.sum_congr rfl (fun u _ => term u), ← Finset.mul_sum]
  have hsum : ∑ u : ZMod n, ζ ^ u.val = ∑ j ∈ Finset.range n, ζ ^ j := by
    refine Finset.sum_nbij' (fun u => u.val) (fun j => (j : ZMod n)) ?_ ?_ ?_ ?_ ?_
    · intro u _; simpa using ZMod.val_lt u
    · intro j _; simp
    · intro u _; simp
    · intro j hj
      exact ZMod.val_cast_of_lt (by simpa using hj)
    · intro u _; rfl
  rw [hsum]
  by_cases hkl : k = l
  · subst hkl
    have : ζ = 1 := by rw [hζ, sub_self, mul_zero, zero_div, Complex.exp_zero]
    simp [this, hn']
  · rw [Matrix.one_apply_ne hkl]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hkl
      apply ZMod.val_injective n
      symm
      refine eq_of_exp_aux hn (ZMod.val_lt l) (ZMod.val_lt k) ?_
      have : 2 * (Real.pi : ℂ) * Complex.I * (l.val : ℂ) / (n : ℂ) =
          2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ) +
            2 * (Real.pi : ℂ) * Complex.I * ((l.val : ℂ) - k.val) / (n : ℂ) := by ring
      rw [this, Complex.exp_add, ← hζ, h1, mul_one]
    have hζn : ζ ^ n = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((l.val : ℂ) - k.val) / (n : ℂ)) =
          (((l.val : ℤ) - k.val : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hζ1, hζn, sub_self, zero_div, mul_zero]
