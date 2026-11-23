-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_quadrant_gaussian_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:58:31.705499+00:00
-- url     : https://prove2.me/submissions/f6f0ebb8-b7aa-422b-9c91-9bad061e5225

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open scoped Real
namespace CQAngular

private theorem determinant (z : ℂ) : ‖1-z^2‖^2=(1-‖z‖^2)^2+4*z.im^2 := by
  rw [Complex.sq_norm (1-z^2),Complex.sq_norm z]
  simp only [Complex.normSq_apply,pow_two,Complex.sub_re,Complex.one_re,
    Complex.mul_re,Complex.sub_im,Complex.one_im,Complex.mul_im]
  ring

private theorem determinantLower (z : ℂ) : 2*|z.im| ≤ ‖1-z^2‖ := by
  have h := determinant z
  have hs : (2*|z.im|)^2 ≤ ‖1-z^2‖^2 := by
    rw [h,mul_pow,sq_abs]
    nlinarith only [sq_nonneg (1-‖z‖^2)]
  exact le_of_sq_le_sq hs (norm_nonneg _)

private theorem sine (s : ℝ) : Real.sin (2 * Real.arctan (s^2))=2*s^2/(1+s^4) := by
  rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
  rw [show (s^2)^2=s^4 by ring]
  have he : 0<1+s^4 := by positivity
  field_simp [(Real.sqrt_pos.mpr he).ne',he.ne']
  rw [Real.sq_sqrt he.le]


private theorem sine_reflected (s θ : ℝ)
    (hθ : let a := 2*Real.arctan (s^2)
          θ=a ∨ θ=Real.pi-a ∨ θ=Real.pi+a ∨ θ=2*Real.pi-a) :
    |Real.sin θ| = 2*s^2/(1+s^4) := by
  have hp : 0≤2*s^2/(1+s^4) := by positivity
  rcases hθ with h|h|h|h <;> rw [h] <;>
    simp [Real.sin_add,Real.sin_sub,sine,abs_of_nonneg hp]

end CQAngular
open CQAngular

theorem solution (r s θ : ℝ) (hr : (99999:ℝ)/100000≤r) (hs : s∈Set.Icc 0 1)
    (hθ : let a := 2*Real.arctan (s^2)
          θ=a ∨ θ=Real.pi-a ∨ θ=Real.pi+a ∨ θ=2*Real.pi-a) :
    ((2 / Real.pi)*(4*s/(1+s^4))) * (2/Real.sqrt ‖1-(circleMap 0 r θ)^2‖) ≤ 2.55 := by
  rcases hs.1.eq_or_lt with hzero|hspos
  · rw [← hzero]; norm_num
  let D := ‖1-(circleMap 0 r θ)^2‖
  have hrp : 0<r := by linarith
  have den : 0<1+s^4 := by positivity
  have hrad := determinantLower (circleMap 0 r θ)
  rw [circleMap_zero_im,abs_mul,abs_of_pos hrp,sine_reflected s θ hθ] at hrad
  change 2*(r*(2*s^2/(1+s^4)))≤D at hrad
  have hz : 4*r*s^2≤D*(1+s^4) := by
    apply (div_le_iff₀ den).mp
    calc
      _ = 2*(r*(2*s^2/(1+s^4))) := by ring
      _ ≤ _ := hrad
  have hd : 0<D := by
    by_contra! hn
    have := mul_nonpos_of_nonpos_of_nonneg hn den.le
    nlinarith only [hz,this,mul_pos hrp (sq_pos_of_pos hspos)]
  have hsqrt : 0<Real.sqrt D := Real.sqrt_pos.mpr hd
  have hD : D*(1+s^4)≤(1+s^4)^2*D := by
    nlinarith only [mul_nonneg (mul_nonneg hd.le den.le) (show 0≤s^4 by positivity)]
  have hr' : (0.99999:ℝ)^2≤r := by norm_num at hr ⊢; linarith
  have hS : 2*0.99999*s ≤ (1+s^4)*Real.sqrt D := by
    apply le_of_sq_le_sq _ (mul_nonneg den.le hsqrt.le)
    rw [mul_pow (1+s^4),Real.sq_sqrt hd.le]
    nlinarith only [mul_le_mul_of_nonneg_right hr' (sq_nonneg s),hz,hD]
  have hn : 16*s ≤ (2.55*Real.pi)*((1+s^4)*Real.sqrt D) := by
    calc
      _ ≤ (2.55*3.14)*(2*0.99999*s) := by nlinarith only [hspos]
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left Real.pi_gt_d2.le (by norm_num)) hS
        (by positivity) (by positivity)
  change ((2/Real.pi)*(4*s/(1+s^4)))*(2/Real.sqrt D) ≤ 2.55
  calc
    _ = (16*s)/(Real.pi*((1+s^4)*Real.sqrt D)) := by
      field_simp [Real.pi_ne_zero,den.ne',hsqrt.ne'] <;> ring
    _ ≤ _ := (div_le_iff₀ (mul_pos Real.pi_pos (mul_pos den hsqrt))).2 (by linarith only [hn])
