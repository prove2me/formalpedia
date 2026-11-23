-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_boundary_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:10:30.926469+00:00
-- url     : https://prove2.me/submissions/a6622ff4-32d8-447f-8c9a-39d2be7247e5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Complex Set

private theorem reciprocal_half (w : ℂ) (hw : ‖w‖ ≤ 1) (hne : 1-w ≠ 0) :
    (1/2 : ℝ) ≤ ((1-w)⁻¹).re := by
  have hn : normSq w ≤ 1 := by
    rw [normSq_eq_norm_sq]
    nlinarith only [hw, norm_nonneg w, mul_nonneg (sub_nonneg.mpr hw) (show 0 ≤ 1+‖w‖ by positivity)]
  rw [inv_re, le_div_iff₀ (normSq_pos.mpr hne)]
  simp only [normSq_apply, sub_re, one_re, sub_im, one_im, zero_sub, neg_mul_neg] at hn ⊢
  linarith only [hn]

private theorem real_part_range (z : ℂ) (hz : ‖z‖ = 1) :
    let a : ℝ := 0.34101124^2
    let b : ℝ := 0.05276111^2
    |(z-(a:ℂ)*z^3+(b:ℂ)*z^5).re| ≤ 1-a+b := by
  dsimp only
  let a : ℝ := 0.34101124^2
  let b : ℝ := 0.05276111^2
  let P (x : ℝ) := (1+3*a+5*b)*x - (4*a+20*b)*x^3 + 16*b*x^5
  have upper (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) : P x ≤ 1-a+b := by
    have hu : 0 ≤ 1+x := by linarith only [hx.1]
    have hv : 0 ≤ 1-x := sub_nonneg.mpr hx.2
    let u := 1+x
    let v := 1-x
    have hu' : 0 ≤ u := hu
    have hv' : 0 ≤ v := hv
    have hint : 32*(1-a+b-P x) =
        (2-2*a+2*b)*v^5 + (8+8*a-40*b)*u*v^4 + (12+4*a+220*b)*u^2*v^3 +
        (8-24*a-200*b)*u^3*v^2 + (2-18*a+50*b)*u^4*v := by dsimp [P,u,v]; ring
    have h1 : 0 ≤ 2-2*a+2*b := by norm_num [a,b]
    have h2 : 0 ≤ 8+8*a-40*b := by norm_num [a,b]
    have h3 : 0 ≤ 12+4*a+220*b := by norm_num [a,b]
    have h4 : 0 ≤ 8-24*a-200*b := by norm_num [a,b]
    have h5 : 0 ≤ 2-18*a+50*b := by norm_num [a,b]
    have hp : 0 ≤ 32*(1-a+b-P x) := by rw [hint]; positivity
    linarith only [hp]
  have hz' : z.re^2 + z.im^2 = 1 := by
    have := normSq_eq_norm_sq z
    rw [hz] at this
    simpa [normSq_apply, sq] using this
  have h3 : (z^3).re = 4*z.re^3-3*z.re := by
    simp only [pow_succ, pow_zero, one_mul, mul_re, mul_im]
    linear_combination (-3*z.re)*hz'
  have h5 : (z^5).re = 16*z.re^5-20*z.re^3+5*z.re := by
    simp only [pow_succ, pow_zero, one_mul, mul_re, mul_im]
    linear_combination (-15*z.re^3+5*z.re*z.im^2+5*z.re)*hz'
  have heq : (z-(a:ℂ)*z^3+(b:ℂ)*z^5).re = P z.re := by
    rw [add_re, sub_re, re_ofReal_mul, re_ofReal_mul, h3, h5]
    dsimp only [P]
    ring
  change |(z-(a:ℂ)*z^3+(b:ℂ)*z^5).re| ≤ 1-a+b
  rw [heq, abs_le]
  have hx : z.re ∈ Icc (-1:ℝ) 1 := abs_le.mp ((abs_re_le_norm z).trans hz.le)
  have hl := upper (-z.re) ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
  have hu := upper z.re hx
  dsimp only [P] at hl hu ⊢
  constructor <;> linarith only [hl, hu]

theorem solution (z : ℂ) (hz : ‖z‖ = 1) :
    let a : ℝ := 0.34101124^2
    let b : ℝ := 0.05276111^2
    let ρ := (z-(a:ℂ)*z^3+(b:ℂ)*z^5) / ((1+a+b : ℝ) : ℂ)
    0.3724 ≤ ‖1-ρ^2‖ ∧ (1/2 : ℝ) ≤ ((1-ρ^2)⁻¹).re - |(ρ/(1-ρ^2)).re| := by
  let a : ℝ := 0.34101124^2
  let b : ℝ := 0.05276111^2
  let V : ℝ := 1+a+b
  let ρ := (z-(a:ℂ)*z^3+(b:ℂ)*z^5) / (V:ℂ)
  change 0.3724 ≤ ‖1-ρ^2‖ ∧ (1/2 : ℝ) ≤ ((1-ρ^2)⁻¹).re - |(ρ/(1-ρ^2)).re|
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hV : 0 < V := by dsimp [V]; positivity
  have hvnorm : ‖(V:ℂ)‖ = V := by simp [Real.norm_eq_abs, abs_of_pos hV]
  have hn : ‖ρ‖ ≤ 1 := by
    rw [show ‖ρ‖ = ‖z-(a:ℂ)*z^3+(b:ℂ)*z^5‖ / V by rw [← hvnorm]; exact norm_div ..,
      div_le_one hV]
    calc
      _ ≤ ‖z-(a:ℂ)*z^3‖ + ‖(b:ℂ)*z^5‖ := norm_add_le ..
      _ ≤ (‖z‖ + ‖(a:ℂ)*z^3‖) + ‖(b:ℂ)*z^5‖ := add_le_add_left (norm_sub_le ..) _
      _ = V := by simp [V, norm_mul, norm_pow, hz, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hreal : |ρ.re| ≤ (1-a+b)/V := by
    change |((z-(a:ℂ)*z^3+(b:ℂ)*z^5)/(V:ℂ)).re| ≤ _
    rw [div_ofReal_re, abs_div, abs_of_pos hV]
    exact div_le_div_of_nonneg_right (real_part_range z hz) hV.le
  have hgap : (0.3724 : ℝ) ≤ 1-((1-a+b)/V)^2 := by norm_num [V,a,b]
  have hs : ρ.re^2 ≤ ((1-a+b)/V)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg ρ.re) hreal 2
  have hd : 0.3724 ≤ ‖1-ρ^2‖ := by
    apply le_trans _ (re_le_norm _)
    rw [sub_re, one_re, pow_two, mul_re]
    nlinarith only [hgap,hs,sq_nonneg ρ.im]
  have hne : 1-ρ^2 ≠ 0 := norm_ne_zero_iff.mp (by linarith only [hd])
  have h1 : 1-ρ ≠ 0 := by intro h; have h' : ρ = 1 := (sub_eq_zero.mp h).symm; simp [h'] at hne
  have h2 : 1+ρ ≠ 0 := by
    intro h
    have h' : ρ = -1 := by linear_combination h
    norm_num [h'] at hne
  have hm := reciprocal_half ρ hn h1
  have hp := reciprocal_half (-ρ) (by simpa using hn) (by simpa using h2)
  rw [sub_neg_eq_add] at hp
  have hpl : (1-ρ^2)⁻¹ + ρ/(1-ρ^2) = (1-ρ)⁻¹ := by field_simp; ring
  have hmi : (1-ρ^2)⁻¹ - ρ/(1-ρ^2) = (1+ρ)⁻¹ := by field_simp; ring
  rw [← hpl, add_re] at hm
  rw [← hmi, sub_re] at hp
  refine ⟨hd, ?_⟩
  rw [le_sub_comm, abs_le]
  constructor <;> linarith
