-- Prove2me | solution 1 for MasulloRH.quarter_shift_gaussian_exterior_energy
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:36.2813+00:00
-- url     : https://prove2.me/submissions/0b38ddf6-7295-4e32-ba9d-cfa8b8ef311b

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Theorems.Thm_MasulloRH_theta_norm_le_dyadic_on_tails
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_finite_theta_residual_tail_bound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation

private theorem coeff_pos (i : Fin 25) : 0 ≤ (coeff i : ℝ) := by
  exact_mod_cast (show ∀ i : Fin 25, 0 ≤ coeff i by decide +kernel) i
private theorem sh (i : Fin 25) : -2 ≤ (shift i : ℝ) ∧ (shift i : ℝ) ≤ 4 := by
  exact_mod_cast (show ∀ i : Fin 25, -2 ≤ shift i ∧ shift i ≤ 4 by decide +kernel) i

private theorem atom_sum (x a t : ℝ) (ht : 0 ≤ t) (hp : ‖pulse 0 x‖ ≤ a)
    (hθ : ∀ i : Fin 25, ‖theta (x-(shift i:ℝ))‖ ≤ t) :
    ‖err x‖ ≤ a+2*t := by
  have hc : (∑ i : Fin 25, (coeff i:ℝ)) ≤ 2 := by
    exact_mod_cast (show (∑ i : Fin 25, coeff i) ≤ 2 by decide +kernel)
  have hcoef (i : Fin 25) : ‖(coeff i : ℂ)‖ = (coeff i:ℝ) := by
    rw [← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (coeff_pos i)]
  apply (norm_sub_le _ _).trans
  apply add_le_add hp
  calc
    _ ≤ ∑ i : Fin 25, ‖(coeff i:ℂ) * theta (x-(shift i:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 25, (coeff i:ℝ)*t := by
      apply Finset.sum_le_sum; intro i _
      rw [norm_mul,hcoef]
      exact mul_le_mul_of_nonneg_left (hθ i) (coeff_pos i)
    _ ≤ 2*t := by rw [← Finset.sum_mul];exact mul_le_mul_of_nonneg_right hc ht

private theorem pulse_norm (x : ℝ) : ‖pulse 0 x‖ ≤ Real.exp (-(x^2)) := by
  have hs : 1 ≤ Real.sqrt Real.pi := Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_three])
  have h : pulse 0 x = ((1/Real.sqrt Real.pi * Real.exp (-(x^2)):ℝ):ℂ) := by
    unfold pulse;push_cast;simp
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le ((div_le_one (by positivity)).2 hs)

private theorem nat_exp (n : ℕ) : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
  simpa using (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Real.exp_one_gt_two.le n).trans_eq
    (Real.exp_nat_mul 1 n).symm
private theorem decay49 : Real.exp (-49) ≤ 1/(2:ℝ)^49 := by
  rw [Real.exp_neg,← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (nat_exp 49)

private theorem right_theta (x y : ℝ) (hx : 7 ≤ x) (hy : y ≤ 4) :
    ‖theta (x-y)‖ ≤ 24*Real.exp (-49)*Real.exp (-2*(x-7)) := by
  let z := x-y
  let A := Real.pi*(Real.exp z)^2
  have h6 : (64:ℝ) ≤ Real.exp 6 := by exact (show (64:ℝ) ≤ 2^6 by norm_num).trans (nat_exp 6)
  have ht : 64*(1+2*(x-7)) ≤ Real.exp (2*z) := by
    calc 64*(1+2*(x-7)) ≤ Real.exp 6 * Real.exp (2*(x-7)) :=
           mul_le_mul h6 (by linarith [Real.add_one_le_exp (2*(x-7))]) (by linarith) (Real.exp_pos _).le
         _ ≤ _ := by rw [←Real.exp_add];apply Real.exp_le_exp.mpr;dsimp [z];linarith
  have hA : 49+2*(x-7) ≤ A := by
    have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have he : Real.exp (2*z) = (Real.exp z)^2 := by simpa using Real.exp_nat_mul z 2
    have hh := mul_le_mul_of_nonneg_right hπ (sq_nonneg (Real.exp z))
    dsimp [A]; rw [he] at ht;linarith only [ht,hh,hx]
  have h := MasulloRH.theta_gaussian_truncation_error z 0
  norm_num only [Finset.range_zero,Finset.sum_empty,Nat.cast_zero,zero_add,
    one_pow,mul_zero,mul_one,sub_zero,neg_mul] at h
  change ‖theta z‖ ≤ 12*Real.exp (-A)/(1-Real.exp (-(A*3))) at h
  have hd : Real.exp (-(A*3)) ≤ 1/2 := by
    calc _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
         _ = 1/Real.exp 1 := by rw [Real.exp_neg,one_div]
         _ ≤ _ := one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
  have hg : ‖theta z‖ ≤ 24*Real.exp (-A) := by
    apply h.trans
    apply (div_le_iff₀ (by linarith : 0<1-Real.exp (-(A*3)))).2
    nlinarith [mul_nonneg (Real.exp_pos (-A)).le
      (show 0≤1/2-Real.exp (-(A*3)) by linarith)]
  apply hg.trans
  rw [mul_assoc,←Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

private theorem left_norm (x : ℝ) (hx : x ≤ -7) : ‖err x‖ ≤ 1/(2:ℝ)^43 := by
  have hp := (pulse_norm x).trans ((Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x+7)] :
    -(x^2) ≤ -49)).trans decay49)
  have hθ (i : Fin 25) : ‖theta (x-(shift i:ℝ))‖ ≤ 1/(2:ℝ)^64 :=
    MasulloRH.theta_norm_le_dyadic_on_tails _ (Or.inl (by linarith [(sh i).1]))
  exact (atom_sum x _ _ (by positivity) hp hθ).trans (by norm_num)

private theorem right_norm (x : ℝ) (hx : 7 ≤ x) :
    ‖err x‖ ≤ (1/(2:ℝ)^43)*Real.exp (-2*(x-7)) := by
  let e := Real.exp (-2*(x-7))
  have hp : ‖pulse 0 x‖ ≤ Real.exp (-49)*e := by
    dsimp [e];rw [←Real.exp_add]
    apply (pulse_norm x).trans
    apply Real.exp_le_exp.mpr;nlinarith [sq_nonneg (x-7)]
  have h := atom_sum x _ _ (by positivity) hp (fun i => right_theta x _ hx (sh i).2)
  have ht : 49*Real.exp (-49) ≤ 1/(2:ℝ)^43 := by linarith only [decay49]
  apply h.trans
  calc _ = (49*Real.exp (-49))*e := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le

theorem solution (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖err x‖^2) ∧
    energy c b err - (∫ x : ℝ in Icc (-7) 7, Real.exp (2*c*x+2*b*|x|)*‖err x‖^2)
      ≤ 1/100000000000000 := by
  let F (x : ℝ) := Real.exp (2*c*x+2*b*|x|)*‖err x‖^2
  have hshift (i : Fin 25) : |(shift i : ℝ)-Real.log 2| ≤ 7 := by
    rw [abs_le]
    have h0 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    constructor <;> linarith [(sh i).1,(sh i).2]
  let F0 (x : ℝ) := Real.exp (2*(3/4)*x+2*0*|x|)*‖err x‖^2
  have h0 : Integrable F0 :=
    (MasulloRH.finite_theta_residual_tail_bound 25 0 (3/4) 0 7 _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hshift).1
  let ratio (x : ℝ) := Real.exp ((2*c-2*(3/4))*x+2*b*|x|)
  have hc : Continuous ratio := by unfold ratio;fun_prop
  have hrepr : F = ratio*F0 := by
    funext x;dsimp only [F,F0,ratio,Pi.mul_apply];rw [←mul_assoc,←Real.exp_add];congr 2;ring
  have hm : AEStronglyMeasurable F := by rw [hrepr];exact hc.aestronglyMeasurable.mul h0.1
  have hinner : IntegrableOn F (Icc (-7:ℝ) 7) := by
    rw [hrepr];exact IntegrableOn.continuousOn_mul hc.continuousOn h0.integrableOn isCompact_Icc
  let C : ℝ := (1/(2:ℝ)^43)^2 * Real.exp 21
  let g (x : ℝ) := Real.exp (-|x|)
  have hg : (∫ x, g x) = 2 := by
    dsimp [g];rw [integral_comp_abs (f:=fun x => Real.exp (-x)),integral_exp_neg_Ioi_zero];ring
  have hgi : Integrable g := by
    by_contra h;rw [integral_undef h] at hg;norm_num at hg
  have hC : 0≤C := by dsimp [C]; positivity
  have hdom (x : ℝ) (hx : x ∈ (Icc (-7:ℝ) 7)ᶜ) : F x ≤ C*g x := by
    have hx' : x < -7 ∨ 7 < x := by
      by_cases u : x < -7
      · exact Or.inl u
      · exact Or.inr (lt_of_not_ge (fun v => hx ⟨le_of_not_gt u,v⟩))
    rcases hx' with h|h
    · have w : Real.exp (2*c*x+2*b*|x|) ≤ Real.exp x := by
        apply Real.exp_le_exp.mpr;rw [abs_of_nonpos (by linarith)]
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(c-b)-1 by linarith) (show x≤0 by linarith)]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (left_norm x h.le) 2
      have hm := mul_le_mul w h2 (sq_nonneg _) (Real.exp_pos _).le
      have he : 1 ≤ Real.exp 21 := Real.one_le_exp (by norm_num)
      have hg' : g x=Real.exp x := by dsimp [g];rw [abs_of_nonpos (by linarith),neg_neg]
      rw [hg'];apply hm.trans
      dsimp [C]; nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg (1/(2:ℝ)^43)) (sub_nonneg.mpr he)) (Real.exp_pos x).le]
    · have w : Real.exp (2*c*x+2*b*|x|) ≤ Real.exp (2*x) := by
        apply Real.exp_le_exp.mpr;rw [abs_of_nonneg (by linarith)]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (show 0≤x by linarith)]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (right_norm x h.le) 2
      apply (mul_le_mul w h2 (sq_nonneg _) (Real.exp_pos _).le).trans
      have he : Real.exp (2*x)*(Real.exp (-2*(x-7)))^2 ≤ Real.exp 21 * Real.exp (-x) := by
        rw [← Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
        apply Real.exp_le_exp.mpr;push_cast;linarith
      dsimp [C,g];rw [abs_of_nonneg (by linarith),mul_pow]
      nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (1/(2:ℝ)^43))]
  have hext : IntegrableOn F (Icc (-7:ℝ) 7)ᶜ := by
    apply (hgi.const_mul C).integrableOn.mono' hm.restrict
    apply (ae_restrict_iff' measurableSet_Icc.compl).2 (Filter.Eventually.of_forall _)
    intro x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤F x by dsimp [F];positivity)]
    exact hdom x hx
  have hi : Integrable F := by
    have hu := integrableOn_union.mpr ⟨hinner,hext⟩
    simpa using hu
  refine ⟨hi,?_⟩
  have hcomp := integral_add_compl (μ:=volume) (s:=Icc (-7:ℝ) 7) measurableSet_Icc hi
  have hj := setIntegral_mono_on hi.integrableOn (hgi.const_mul C).integrableOn
    measurableSet_Icc.compl hdom
  have hk := setIntegral_le_integral (s:=(Icc (-7:ℝ) 7)ᶜ) (hgi.const_mul C)
    (Filter.Eventually.of_forall fun x => mul_nonneg hC (Real.exp_pos _).le)
  have he21 : Real.exp 21 ≤ (3:ℝ)^21 := by
    have hh := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 21
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using hh
  have hsmall : C*2 ≤ 1/100000000000000 := by dsimp [C];linarith only [he21]
  change (∫ x, F x) - (∫ x in Icc (-7:ℝ) 7, F x) ≤ _
  have heq : (∫ x : ℝ, C*g x) = C*2 := by rw [integral_const_mul,hg]
  rw [heq] at hk
  linarith only [hcomp,hj,hk,hsmall]
