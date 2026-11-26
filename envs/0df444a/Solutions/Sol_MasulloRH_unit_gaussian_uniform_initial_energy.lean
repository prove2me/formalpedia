-- Prove2me | solution 1 for MasulloRH.unit_gaussian_uniform_initial_energy
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:23:42.689641+00:00
-- url     : https://prove2.me/submissions/d0161ebb-ddc4-438b-b2d7-a45fe657478c

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Real MasulloRH.GaussianApproximation

private theorem weight_upper (c b x : ℝ) (hl : 1/2≤c-b) (hr : c+b≤7/8) :
    exp (2*c*x+2*b*|x|) ≤ exp ((7/4)*x)+1/4 := by
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    have up : 2*c*x+2*b*x ≤ (7/4)*x := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) hx]
    exact (exp_le_exp.2 up).trans (le_add_of_nonneg_right (by norm_num))
  · rw [abs_of_nonpos hx]
    have h : 2*c*x+2*b*(-x)≤x := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hx]
    have h₂ : exp (2*x)≤exp ((7/4)*x) := exp_le_exp.2 (by linarith)
    rw [two_mul,exp_add] at h₂
    exact (exp_le_exp.2 h).trans (by nlinarith [sq_nonneg (exp x-1/2)])

private theorem pulse_sq (x : ℝ) : ‖pulse 0 x‖^2=(1/π)*exp (-2*x^2) := by
  have e : pulse 0 x = ((1/sqrt π*exp (-(x^2)):ℝ):ℂ) := by
    simp only [pulse,zero_add,one_mul,Complex.ofReal_mul,Complex.ofReal_exp,
      Complex.ofReal_neg,Complex.ofReal_pow]
  rw [e,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,div_pow,one_pow,
    Real.sq_sqrt Real.pi_pos.le,←Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The zero combination already has weighted energy below seven tenths on
every fixed-Gaussian test window, including the limiting endpoint weights. -/
theorem solution (c b : ℝ) (hl : 1/2≤c-b) (hr : c+b≤7/8) :
    energy c b (pulse 0)<7/10 := by
  let g (x : ℝ) := exp (-2*x^2)
  let h (x : ℝ) := (1/π)*(exp (49/128)*g (x-7/16)+(1/4)*g x)
  have gi : Integrable g := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<2)
  have g₁ : Integrable (fun x : ℝ => exp (49/128)*g (x-7/16)) :=
    (gi.comp_sub_right _).const_mul _
  have g₂ : Integrable (fun x : ℝ => (1/4)*g x) := gi.const_mul _
  have hi : Integrable h := (g₁.add g₂).const_mul _
  have bound : energy c b (pulse 0) ≤ ∫ x : ℝ, h x := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun _ => mul_nonneg (exp_nonneg _) (sq_nonneg _))) hi
    apply ae_of_all
    intro x
    change exp (2*c*x+2*b*|x|)*‖pulse 0 x‖^2 ≤ h x
    rw [pulse_sq]
    calc
      _ ≤ (exp ((7/4)*x)+1/4)*((1/π)*exp (-2*x^2)) :=
        mul_le_mul_of_nonneg_right (weight_upper c b x hl hr) (by positivity)
      _ = h x := by
        have id : exp ((7/4)*x)*exp (-2*x^2)=exp (49/128)*g (x-7/16) := by
          dsimp [g]
          rw [←exp_add,←exp_add]
          congr 1
          ring
        dsimp only [h]
        rw [←id]
        dsimp only [g]
        ring
  have val : (∫ x : ℝ, h x)=(1/π)*((exp (49/128)+1/4)*sqrt (π/2)) := by
    dsimp only [h]
    rw [integral_const_mul,integral_add g₁ g₂,integral_const_mul,integral_const_mul,
      integral_sub_right_eq_self,show (∫ x : ℝ, g x)=sqrt (π/2) from integral_gaussian 2,add_mul]
  have h₀ := Real.add_one_le_exp (-(49/512:ℝ))
  rw [Real.exp_neg,←one_div] at h₀
  have cap : exp (49/512)≤512/463 := by linarith [(le_div_iff₀ (exp_pos _)).1 h₀]
  have hsum : exp (49/128)+1/4<7/4 := by
    have he : exp (49/128)=(exp (49/512))^4 := by rw [←Real.exp_nat_mul];norm_num
    rw [he]
    have hp := pow_le_pow_left₀ (exp_nonneg _) cap 4
    norm_num at hp
    linarith
  have hroot : sqrt (π/2)<(2/5)*π := by
    apply (sq_lt_sq₀ (sqrt_nonneg _) (by positivity)).1
    rw [sq_sqrt (by positivity)]
    nlinarith [mul_pos pi_pos (show 0<π-25/8 by linarith [pi_gt_d2])]
  rw [val] at bound
  apply bound.trans_lt
  calc
    _ < (1/π)*((7/4)*((2/5)*π)) := by gcongr
    _ = 7/10 := by field_simp;ring
