-- Prove2me | solution 1 for MasulloRH.height_two_theta_six_tail_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:29:47.887802+00:00
-- url     : https://prove2.me/submissions/2fe5d4be-3667-4454-ac8a-a66f01726ffc

import Definitions.Def_MasulloRH_HeightTwoCurvature
import Theorems.Thm_MasulloRH_second_deriv_finite_translated_sum
import Theorems.Thm_MasulloRH_gaussian_atom_value_and_second_derivative_decay
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH.HeightTwoCurvature

private def rho (b : Bool) : ℝ := if b then -1 else 0
private def rate (b : Bool) : ℝ := if b then -2 else 2
private noncomputable def mass (b : Bool) (h : ℝ) := (if b then Real.pi/16 else Real.pi)*h^2
private noncomputable def atom (b : Bool) (h z : ℝ) := Real.exp (rho b*z - mass b h*Real.exp (rate b*z))
private def signs (i : Fin 3) : ℝ := ![1,-3,2] i
private def modes (i : Fin 3) : ℝ := ![1,2,4] i
private def coeff (b : Bool) (i : Fin 6 × Fin 3) := (if b then 1 else 2)*signs i.2
private def scaleMode (i : Fin 6 × Fin 3) : ℝ := ((i.1.val:ℝ)+1)*modes i.2

private theorem exponent (b : Bool) (h z : ℝ) :
    mass b h * Real.exp (rate b*z) = Real.pi*(h*Real.exp (arg b z))^2 := by
  cases b
  · simp only [mass,rate,arg,Bool.false_eq_true,↓reduceIte]
    rw [show 2*z = z+z by ring,Real.exp_add]; ring
  · simp only [mass,rate,arg,↓reduceIte]
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<4),
      show (-2:ℝ)*z = -z + -z by ring, Real.exp_add]; ring

private theorem atom_form (b : Bool) (h z : ℝ) :
    atom b h z = (if b then Real.exp (-z) else 1) * Real.exp (-Real.pi*(h*Real.exp (arg b z))^2) := by
  unfold atom
  rw [exponent, sub_eq_add_neg, Real.exp_add, ← neg_mul]
  cases b <;> simp [rho]

private theorem theta_form (b : Bool) (z : ℝ) :
    thetaSix b z = ∑ i : Fin 6 × Fin 3, coeff b i * atom b (scaleMode i) z := by
  unfold thetaSix
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Fin.sum_univ_three]
  simp only [coeff,scaleMode,signs,modes,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,atom_form]
  cases b <;> simp only [factor,Bool.false_eq_true,↓reduceIte]
    <;> ring_nf

private theorem parameters (b : Bool) (h z : ℝ) (hh : 1 ≤ h)
    (hc : (b = true ∧ z ≤ -5/2) ∨ (b = false ∧ 9/8 ≤ z)) :
    28 ≤ mass b h*Real.exp (rate b*z) ∧ 8*(rho b*z) ≤ mass b h*Real.exp (rate b*z) := by
  have hp : (31/10:ℝ) ≤ Real.pi := (by norm_num : (31/10:ℝ) ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le
  have hs : 1 ≤ h^2 := by nlinarith [sq_nonneg (h-1)]
  have he (n : ℕ) : (271/100:ℝ)^n ≤ Real.exp (n:ℝ) := by
    have h1 : (271/100:ℝ) ≤ Real.exp 1 := (by norm_num : (271/100:ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
    simpa using (pow_le_pow_left₀ (by norm_num) h1 n).trans_eq (Real.exp_nat_mul 1 n).symm
  rcases hc with ⟨rfl,hz⟩ | ⟨rfl,hz⟩
  · simp only [mass,rate,rho,↓reduceIte,neg_one_mul]
    have h5 : (145:ℝ) ≤ Real.exp 5 := (by norm_num : (145:ℝ) ≤ (271/100)^5).trans (by simpa using he 5)
    have hex : 145*(1+(-2*z-5)) ≤ Real.exp (-2*z) := by
      calc _ ≤ Real.exp 5 * Real.exp (-2*z-5) := mul_le_mul h5
                 (by linarith [Real.add_one_le_exp (-2*z-5)]) (by linarith) (Real.exp_pos _).le
           _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hm : (31/10:ℝ)/16 ≤ Real.pi/16*h^2 := by
      calc _ ≤ Real.pi/16 := by linarith
           _ ≤ _ := le_mul_of_one_le_right (by positivity) hs
    have hbound := mul_le_mul hm hex (by nlinarith : 0 ≤ 145*(1+(-2*z-5))) (by positivity)
    constructor <;> linarith
  · simp only [mass,rate,rho,Bool.false_eq_true,↓reduceIte,zero_mul]
    have he2 : (271/100:ℝ)^2 ≤ Real.exp 2 := by simpa using he 2
    have hq : (5/4:ℝ) ≤ Real.exp (2*z-2) := by linarith [Real.add_one_le_exp (2*z-2)]
    have hex : (271/100:ℝ)^2*(5/4) ≤ Real.exp (2*z) := by
      calc _ ≤ Real.exp 2 * Real.exp (2*z-2) := mul_le_mul he2 hq (by norm_num) (Real.exp_pos _).le
           _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hm : (31/10:ℝ) ≤ Real.pi*h^2 := hp.trans (le_mul_of_one_le_right Real.pi_pos.le hs)
    have hbound := mul_le_mul hm hex (by norm_num : 0 ≤ (271/100:ℝ)^2*(5/4)) (by positivity)
    constructor <;> linarith

theorem solution (b : Bool) (z : ℝ)
    (hc : (b = true ∧ z ≤ -5/2) ∨ (b = false ∧ 9/8 ≤ z)) :
    |thetaSix b z| ≤ 1/200000000 ∧ |deriv (deriv (thetaSix b)) z| ≤ 1/200 ∧
      thetaTail b z ≤ 1/1000000000 := by
  let I := Fin 6 × Fin 3
  let f (i : I) := atom b (scaleMode i)
  have hf (i : I) : ContDiff ℝ 2 (f i) := by change ContDiff ℝ 2 (fun x => Real.exp (rho b*x - mass b (scaleMode i)*Real.exp (rate b*x))); fun_prop
  have hshape : thetaSix b = fun y => ∑ i : I, coeff b i * f i (y-0) := by
    funext y; simpa [f] using theta_form b y
  have hcoef (i : I) : |coeff b i| ≤ 6 := by
    obtain ⟨k,i⟩ := i
    cases b <;> fin_cases i <;> norm_num [coeff,signs,Matrix.cons_val_zero,Matrix.cons_val_succ]
  have hab (i : I) : |f i z| ≤ 1/(27/10:ℝ)^24 ∧
      |deriv (deriv (f i)) z| ≤ 161/(27/10:ℝ)^17 := by
    have hmod : 1 ≤ modes i.2 := by
      obtain ⟨k,i⟩ := i
      fin_cases i <;> norm_num [modes,Matrix.cons_val_zero,Matrix.cons_val_succ]
    have hn : 1 ≤ scaleMode i := one_le_mul_of_one_le_of_one_le
      (by linarith [Nat.cast_nonneg (α:=ℝ) i.1.val]) hmod
    obtain ⟨hu,hz⟩ := parameters b _ z hn hc
    exact MasulloRH.gaussian_atom_value_and_second_derivative_decay _ _ _ z
      (by cases b <;> norm_num [rho]) (by cases b <;> norm_num [rate]) hu hz
  have aggregate (g : I → ℝ) (v : ℝ) (hv : 0 ≤ v) (hg : ∀ i, |g i| ≤ v) :
      |∑ i, coeff b i*g i| ≤ 108*v := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : I, 6*v := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul (hcoef i) (hg i) (abs_nonneg _) (by norm_num)
      _ = _ := by simp [I]; ring
  refine ⟨?_,?_,?_⟩
  · rw [theta_form]
    exact (aggregate _ _ (by positivity) (fun i => (hab i).1)).trans (by norm_num)
  · rw [hshape, MasulloRH.second_deriv_finite_translated_sum f (coeff b) (fun _ => 0) hf, sub_zero]
    exact (aggregate _ _ (by positivity) (fun i => (hab i).2)).trans (by norm_num)
  · let v := Real.pi * (Real.exp (arg b z))^2
    obtain ⟨hu,hz⟩ := parameters b 1 z le_rfl hc
    rw [exponent,one_mul] at hu hz
    change 28 ≤ v at hu
    change 8*(rho b*z) ≤ v at hz
    have hden : Real.exp (-v*15) ≤ 1/2 := by
      apply (Real.exp_le_exp.mpr (show -v*15 ≤ -1 by linarith)).trans
      rw [Real.exp_neg, ←one_div]
      exact one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
    have hfac : factor b z ≤ Real.exp (rho b*z) := by
      cases b <;> simp [factor,rho]
      linarith [Real.exp_pos (-z)]
    have hfp : 0 ≤ factor b z := by
      cases b <;> simp [factor]
      positivity
    change factor b z*(12*Real.exp ((-Real.pi*(Real.exp (arg b z))^2)*49) /
      (1-Real.exp ((-Real.pi*(Real.exp (arg b z))^2)*15))) ≤ _
    rw [neg_mul]
    change factor b z*(12*Real.exp (-v*49)/(1-Real.exp (-v*15))) ≤ _
    have hd : 12*Real.exp (-v*49)/(1-Real.exp (-v*15)) ≤ 24*Real.exp (-v*49) := by
      apply (div_le_iff₀ (by linarith : 0 < 1-Real.exp (-v*15))).2
      nlinarith [mul_nonneg (Real.exp_pos (-v*49)).le (show 0 ≤ 1/2-Real.exp (-v*15) by linarith)]
    have hlim : Real.exp (-40) ≤ 1/(2:ℝ)^40 := by
      rw [Real.exp_neg,←one_div]
      apply one_div_le_one_div_of_le (by norm_num)
      simpa using (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 40).trans_eq (Real.exp_nat_mul 1 40).symm
    calc
      _ ≤ Real.exp (rho b*z)*(24*Real.exp (-v*49)) :=
        (mul_le_mul_of_nonneg_left hd hfp).trans (mul_le_mul_of_nonneg_right hfac (by positivity))
      _ = 24 * Real.exp (rho b*z-v*49) := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf
      _ ≤ 24 * Real.exp (-40) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ ≤ 24 * (1/(2:ℝ)^40) := mul_le_mul_of_nonneg_left hlim (by norm_num)
      _ ≤ _ := by norm_num
