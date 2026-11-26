-- Prove2me | solution 1 for MasulloRH.unit_gaussian_half_scale_two_difference
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:42:14.48267+00:00
-- url     : https://prove2.me/submissions/093ad229-9e4b-48c9-b1a7-b1c02f4dd26c

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
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

private noncomputable def atom (n x : ℝ) : ℝ := (1/π)*(exp ((7/4)*x)+1/4)*exp (-n*x^2)

private theorem atom_val (n : ℝ) (hn : 0<n) : Integrable (atom n) ∧
    (∫ x : ℝ, atom n x)=(exp (49/(64*n))+1/4)*sqrt (π/n)/π := by
  let g := fun x : ℝ => exp (-n*x^2)
  let u := 7/(8*n)
  have gi : Integrable g := integrable_exp_neg_mul_sq hn
  have g₁ : Integrable (fun x : ℝ => exp (49/(64*n))*g (x-u)) := (gi.comp_sub_right _).const_mul _
  have g₂ : Integrable (fun x : ℝ => (1/4)*g x) := gi.const_mul _
  have id : atom n = fun x => (1/π)*(exp (49/(64*n))*g (x-u)+(1/4)*g x) := by
    funext x
    have e : exp ((7/4)*x)*g x=exp (49/(64*n))*g (x-u) := by
      dsimp [g,u];rw [←exp_add,←exp_add];congr 1;field_simp;ring
    unfold atom
    dsimp only [g] at e ⊢
    rw [←e];ring
  rw [id]
  refine ⟨(g₁.add g₂).const_mul _,?_⟩
  rw [integral_const_mul,integral_add g₁ g₂,integral_const_mul,integral_const_mul,
    integral_sub_right_eq_self,show (∫ x : ℝ, g x)=sqrt (π/n) from integral_gaussian n]
  ring

private theorem diff_sq (x : ℝ) : ‖pulse 0 x-(1/2:ℂ)*pulse 2 x‖^2 =
    (1/π)*(exp (-2*x^2)-3*exp (-10*x^2)+(9/4)*exp (-18*x^2)) := by
  have hp (n : ℝ) : pulse n x=(((n+1)/sqrt π*exp (-(((n+1)*x)^2)):ℝ):ℂ) := by
    simp only [pulse,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_pow]
  have repr : pulse 0 x-(1/2:ℂ)*pulse 2 x=
      (((1/sqrt π)*(exp (-x^2)-(3/2)*exp (-9*x^2)):ℝ):ℂ) := by
    rw [hp,hp];push_cast;norm_num;ring_nf
  have aa : exp (-x^2)^2=exp (-2*x^2) := by rw [sq,←exp_add];congr 1;ring
  have ab : exp (-x^2)*exp (-9*x^2)=exp (-10*x^2) := by rw [←exp_add];congr 1;ring
  have bb : exp (-9*x^2)^2=exp (-18*x^2) := by rw [sq,←exp_add];congr 1;ring
  rw [repr,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,div_pow,one_pow,sq_sqrt pi_pos.le]
  congr 1;nlinarith [aa,ab,bb]

private theorem atom_bounds : (∫ x : ℝ, atom 2 x)<69/100 ∧
    11/50<(∫ x : ℝ, atom 10 x) ∧ (∫ x : ℝ, atom 18 x)<7/40 := by
  have ecap (x : ℝ) (h : x<1) : exp x ≤ 1/(1-x) := by
    have p := add_one_le_exp (-x);rw [exp_neg,←one_div] at p
    apply (le_div_iff₀ (by linarith)).2;linarith [(le_div_iff₀ (exp_pos _)).1 p]
  have est : exp (49/128)+1/4<69/40 := by
    have e : exp (49/128)=(exp (49/2048))^16 := by rw [←exp_nat_mul];norm_num
    rw [e];have h := pow_le_pow_left₀ (exp_nonneg _) (ecap (49/2048) (by norm_num)) 16
    norm_num at h;linarith
  have est18 : exp (49/1152)+1/4<21/16 := by linarith [ecap (49/1152) (by norm_num)]
  have low10 : 5/4<exp (49/640)+1/4 := by linarith [Real.one_lt_exp_iff.2 (show (0:ℝ)<49/640 by norm_num)]
  have piL : 0<π-25/8 := by linarith [pi_gt_d2]
  have piU : 0<63/20-π := by linarith [pi_lt_d2]
  have s2 : sqrt (π/2)<2/5*π := by
    apply (sq_lt_sq₀ (sqrt_nonneg _) (by positivity)).1;rw [sq_sqrt (by positivity)];nlinarith [mul_pos pi_pos piL]
  have s18 : sqrt (π/18)<2/15*π := by
    apply (sq_lt_sq₀ (sqrt_nonneg _) (by positivity)).1;rw [sq_sqrt (by positivity)];nlinarith [mul_pos pi_pos piL]
  have s10 : 22/125*π<sqrt (π/10) := by
    apply (sq_lt_sq₀ (by positivity) (sqrt_nonneg _)).1;rw [sq_sqrt (by positivity)];nlinarith [mul_pos pi_pos piU]
  rw [(atom_val 2 (by norm_num)).2,(atom_val 10 (by norm_num)).2,(atom_val 18 (by norm_num)).2]
  norm_num only [show (64:ℝ)*2=128 by norm_num,show (64:ℝ)*10=640 by norm_num,show (64:ℝ)*18=1152 by norm_num]
  refine ⟨(div_lt_iff₀ pi_pos).2 ?_,(lt_div_iff₀ pi_pos).2 ?_,(div_lt_iff₀ pi_pos).2 ?_⟩
  · calc _ < (69/40)*(2/5*π) := by gcongr
         _ = _ := by ring
  · calc _ = (5/4)*(22/125*π) := by ring
         _ < _ := by gcongr
  · calc _ < (21/16)*(2/15*π) := by gcongr
         _ = _ := by ring

/-- Comparing the unit Gaussian with half the scale-two Gaussian gives an integrable difference with uniformly bounded weighted energy. -/
theorem solution (c b : ℝ) (hl : 1/2≤c-b) (hr : c+b≤7/8) :
    Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖pulse 0 x-(1/2:ℂ)*pulse 2 x‖^2) ∧
    energy c b (fun x => pulse 0 x-(1/2:ℂ)*pulse 2 x)<17/40 := by
  let major := fun x : ℝ => atom 2 x - 3*atom 10 x + (9/4)*atom 18 x
  have i2 := (atom_val 2 (by norm_num)).1
  have i10 := (atom_val 10 (by norm_num)).1.const_mul 3
  have i18 := (atom_val 18 (by norm_num)).1.const_mul (9/4)
  have mi : Integrable major := (i2.sub i10).add i18
  have dom (x : ℝ) : exp (2*c*x+2*b*|x|)*‖pulse 0 x-(1/2:ℂ)*pulse 2 x‖^2 ≤ major x := by
    apply (mul_le_mul_of_nonneg_right (weight_upper c b x hl hr) (sq_nonneg _)).trans
    apply le_of_eq;rw [diff_sq];dsimp [major,atom];ring
  have hi : Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖pulse 0 x-(1/2:ℂ)*pulse 2 x‖^2) := by
    apply mi.mono' (by unfold pulse;fun_prop);apply ae_of_all;intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (exp_nonneg _) (sq_nonneg _))];exact dom x
  refine ⟨hi,(integral_mono hi mi dom).trans_lt ?_⟩
  dsimp [major]
  have isub : Integrable (fun x => atom 2 x-3*atom 10 x) := i2.sub i10
  rw [integral_add isub i18,integral_sub i2 i10,integral_const_mul,integral_const_mul]
  linarith [atom_bounds.1,atom_bounds.2.1,atom_bounds.2.2]
