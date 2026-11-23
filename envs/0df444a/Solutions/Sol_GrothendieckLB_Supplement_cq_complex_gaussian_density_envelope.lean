-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_complex_gaussian_density_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:21:04.826894+00:00
-- url     : https://prove2.me/submissions/0f352e70-b674-4ff1-b665-487a8441b5c2

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open GrothendieckLB.Supplement.CQPrice

private theorem half_le_inv_re (v : ℂ) (hv : ‖v‖ < 1) : (1/2:ℝ) ≤ ((1+v)⁻¹).re := by
  have hpos : 0 < (1+v).re := by
    have := (abs_lt.mp ((Complex.abs_re_le_norm v).trans_lt hv)).1
    simp only [Complex.add_re,Complex.one_re]
    linarith
  have hn : 1+v ≠ 0 := fun h => by rw [h] at hpos; simpa using hpos
  have hs : ‖v‖^2 < 1 := pow_lt_one₀ (norm_nonneg _) hv (by decide)
  rw [Complex.sq_norm,Complex.normSq_apply] at hs
  rw [Complex.inv_re,le_div_iff₀ (Complex.normSq_pos.mpr hn)]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,zero_add]
  nlinarith

theorem solution (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) :
    ‖density z x y‖ ≤ (2/Real.sqrt ‖1-z^2‖) * (normalTwo x * normalTwo y) := by
  have hm : (1/2:ℝ) ≤ ((1-z)⁻¹).re := by simpa [sub_eq_add_neg] using half_le_inv_re (-z) (by simpa)
  have he : -(((x+y)^2/4)*((1+z)⁻¹).re + ((x-y)^2/4)*((1-z)⁻¹).re) ≤
      -(x^2)/4+ -(y^2)/4 := by
    nlinarith only [mul_le_mul_of_nonneg_left (half_le_inv_re z hz) (sq_nonneg (x+y)),
      mul_le_mul_of_nonneg_left hm (sq_nonneg (x-y))]
  have hd : 0 < ‖1-z^2‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hh : z^2=1 := (sub_eq_zero.mp h).symm
    have hc : ‖z^2‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg _) hz (by decide)
    simpa [hh] using hc
  have hp := Real.sqrt_pos.mpr Real.pi_pos
  have hs := Real.sqrt_pos.mpr hd
  rw [density,norm_mul,norm_div,Complex.norm_cpow_real,Real.rpow_neg (norm_nonneg _),
    ← Real.sqrt_eq_rpow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<2*Real.pi),
    Complex.norm_exp,Complex.neg_re,Complex.add_re,Complex.re_ofReal_mul,Complex.re_ofReal_mul]
  calc
    _ ≤ _ * Real.exp (-(x^2)/4+ -(y^2)/4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by
      rw [Real.exp_add];unfold normalTwo
      field_simp [hp.ne',hs.ne',Real.pi_pos.ne']
      nlinarith [Real.sq_sqrt Real.pi_pos.le]
