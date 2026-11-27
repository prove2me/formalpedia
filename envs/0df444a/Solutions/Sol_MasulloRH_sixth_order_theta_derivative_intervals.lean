-- Prove2me | solution 1 for MasulloRH.sixth_order_theta_derivative_intervals
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:08:48.890679+00:00
-- url     : https://prove2.me/submissions/5a897c27-bd5d-4b26-84be-94ec154268dd

import Theorems.Thm_MasulloRH_horner_interval_and_derivative
import Theorems.Thm_MasulloRH_central_theta_interval_sound
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set MasulloRH MasulloRH.CentralInterval MasulloRH.InteriorEvaluator
open MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation
private abbrev ok := MasulloRH.central_interval_arithmetic_sound
open MasulloRH.HeightTwoCurvature
private noncomputable def mass (b : Bool) (h : ℝ) := (if b then Real.pi/16 else Real.pi)*h^2
private noncomputable def atom (b : Bool) (h z : ℝ) := Real.exp (rho b*z - mass b h*Real.exp (rate b*z))
private def signs (i : Fin 3) : ℝ := ![1,-3,2] i
private def modes (i : Fin 3) : ℝ := ![1,2,4] i
private def atomWeight (b : Bool) (i : Fin 6 × Fin 3) := (if b then 1 else 2)*signs i.2
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
    thetaSix b z = ∑ i : Fin 6 × Fin 3, atomWeight b i * atom b (scaleMode i) z := by
  unfold thetaSix
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Fin.sum_univ_three]
  simp only [atomWeight,scaleMode,signs,modes,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,atom_form]
  cases b <;> simp only [factor,Bool.false_eq_true,↓reduceIte]
    <;> ring_nf


private theorem index_eq (i : Index) : (powerIndex i:ℝ) = (scaleMode i)^2 := by
  obtain ⟨k,t⟩ := i
  fin_cases t <;> norm_num [powerIndex,scaleNat,scaleMode,modes,Matrix.cons_val_zero,Matrix.cons_val_succ]
private theorem sign_eq (i : Index) : (signQ i:ℝ) = signs i.2 := by
  obtain ⟨k,t⟩ := i
  fin_cases t <;> norm_num [signQ,signs,Matrix.cons_val_zero,Matrix.cons_val_succ]
private theorem parameter (b : Bool) (i : Index) (z : ℝ) :
    mass b (scaleMode i)*Real.exp (rate b*z) = (powerIndex i:ℝ)*baseU b z := by
  rw [index_eq]; dsimp [mass,baseU]; ring
private theorem term_eq (b : Bool) (i : Index) (z : ℝ) :
    atomWeight b i*atom b (scaleMode i) z =
    (signQ i:ℝ)*(pref b z*(Real.exp (-baseU b z))^(powerIndex i)) := by
  rw [sign_eq, ←Real.exp_nat_mul]
  unfold atom
  rw [parameter, sub_eq_add_neg, Real.exp_add,←mul_neg]
  cases b <;> simp [atomWeight,pref,rho]
  ring
private theorem param_sound (b : Bool) {a : Box} {z : ℝ} (h : Covers a z) :
    Covers (params b a).u (baseU b z) ∧ Covers (params b a).q (Real.exp (-baseU b z)) ∧
      Covers (params b a).pref (pref b z) := by
  have piOK : Covers piB Real.pi := by
    constructor
    · exact (by norm_num [piB] : ((piB.1:ℚ):ℝ) ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le
    · exact Real.pi_lt_d20.le.trans (by norm_num [piB])
  have hu : Covers (params b a).u (baseU b z) := by
    cases b
    · simpa [params,baseU,rate] using ok.mul_ok piOK (ok.exp_ok (ok.mul_ok (ok.point_ok 2) h))
    · simpa [params,baseU,rate,div_eq_mul_inv] using
        ok.mul_ok (ok.mul_ok piOK (ok.point_ok (1/16))) (ok.exp_ok (ok.mul_ok (ok.point_ok (-2)) h))
  refine ⟨hu,ok.exp_ok (ok.neg_ok hu),?_⟩
  cases b
  · simpa [params,pref] using ok.point_ok 2
  · exact ok.exp_ok (ok.neg_ok h)

private theorem single_error (b : Bool) (z : ℝ) :
    ‖theta z - (thetaSix b z : ℂ)‖ ≤ thetaTail b z := by
  let y := arg b z
  let S (x : ℝ) : ℝ := 2 * ∑ k ∈ Finset.range 6,
    let t := ((k : ℝ) + 1) * Real.exp x
    Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) + 2*Real.exp (-Real.pi*(4*t)^2)
  have h := MasulloRH.theta_gaussian_truncation_error y 6
  have h' : ‖theta y - (S y : ℂ)‖ ≤
      12 * Real.exp (-Real.pi * (Real.exp y)^2 * 49) /
        (1 - Real.exp (-Real.pi * (Real.exp y)^2 * 15)) := by
    simpa only [S, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
      Nat.cast_ofNat, show (6 + 1 : ℝ)^2 = 49 by norm_num,
      show (2*6+3 : ℝ) = 15 by norm_num] using h
  have heq : theta z = (factor b z : ℂ) * theta y := by
    cases b
    · simp [factor, y, arg]
    · exact MasulloRH.theta_reflection z
  have hp : 0 ≤ factor b z := by
    cases b
    · exact zero_le_one
    · exact div_nonneg (Real.exp_pos _).le (by norm_num)
  change ‖theta z - ((factor b z * S y : ℝ) : ℂ)‖ ≤ _
  rw [heq, Complex.ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left h' hp



private theorem exp_power (b : Bool) (i : Index) (x : ℝ) :
    Real.exp (-((powerIndex i:ℝ)*baseU b x)) = Real.exp (-baseU b x)^powerIndex i := by
  rw [← Real.exp_nat_mul];congr 1;ring

private theorem theta_zero (b : Bool) (x : ℝ) : tJet b 0 x = thetaSix b x := by
  rw [theta_form]
  apply Finset.sum_congr rfl
  intro i _
  rw [term_eq,exp_power]
  cases b <;> simp [thetaCoeffs,hornerR]

private theorem poly_step (b : Bool) (n : ℕ) (hn : n < 6) (v : ℝ) :
    hornerSlope (thetaCoeffs b n) v * (rate b*v) +
      hornerR (thetaCoeffs b n) v * (rho b-rate b*v) =
    hornerR (thetaCoeffs b (n+1)) v := by
  interval_cases n <;> cases b <;> norm_num [thetaCoeffs,hornerSlope,hornerR,rho,rate] <;> ring

private theorem atom_der (b : Bool) (i : Index) (n : ℕ) (hn : n < 6) (x : ℝ) :
    let v := fun z : ℝ => (powerIndex i:ℝ)*baseU b z
    let w := fun z : ℝ => pref b z * Real.exp (-v z)
    HasDerivAt (fun z => (signQ i:ℝ)*(hornerR (thetaCoeffs b n) (v z)*w z))
      ((signQ i:ℝ)*(hornerR (thetaCoeffs b (n+1)) (v x)*w x)) x := by
  let v := fun z : ℝ => (powerIndex i:ℝ)*baseU b z
  let w := fun z : ℝ => pref b z*Real.exp (-v z)
  change HasDerivAt (fun z => (signQ i:ℝ)*(hornerR (thetaCoeffs b n) (v z)*w z)) _
    x
  have hv : HasDerivAt v (rate b*v x) x := by
    have h := ((((hasDerivAt_id x).const_mul (rate b)).exp).const_mul
      (if b then Real.pi/16 else Real.pi)).const_mul (powerIndex i:ℝ)
    apply h.congr_deriv
    dsimp [v,baseU];ring
  have hp : HasDerivAt (pref b) (rho b*pref b x) x := by
    cases b
    · change HasDerivAt (fun _ : ℝ => (2:ℝ)) (0*2) x
      simpa using hasDerivAt_const x (2:ℝ)
    · change HasDerivAt (fun t : ℝ => Real.exp (-t)) ((-1)*Real.exp (-x)) x
      simpa using ((hasDerivAt_id x).neg.exp)
  have hw : HasDerivAt w ((rho b-rate b*v x)*w x) x := by
    apply (hp.mul hv.neg.exp).congr_deriv
    dsimp [w];ring
  have h := ((((MasulloRH.horner_interval_and_derivative (thetaCoeffs b n)).1 (v x)).comp x hv).mul hw).const_mul (signQ i:ℝ)
  apply h.congr_deriv
  change _ = (signQ i:ℝ)*(hornerR (thetaCoeffs b (n+1)) (v x)*w x)
  rw [←poly_step b n hn]
  simp only [Function.comp_apply]
  ring

theorem solution :
    (∀ (b : Bool) (n : ℕ), n < 6 → ∀ x : ℝ, HasDerivAt (tJet b n) (tJet b (n+1) x) x) ∧
    (∀ (b : Bool) (n : ℕ) (z : Box) (x : ℝ), Covers z x →
      Covers (thetaJB b n (params b z)) (tJet b n x)) ∧
    (∀ (b : Bool) (z : Box) (x : ℝ), Covers z x → 0 < tailDen (params b z) →
      ‖theta x-(tJet b 0 x:ℂ)‖ ≤ (tailU (params b z):ℝ)) := by
  refine ⟨?_,?_,?_⟩
  · intro b n hn x
    unfold tJet
    exact HasDerivAt.fun_sum (fun i _ => atom_der b i n hn x)
  · intro b n z x hx
    obtain ⟨hu,hq,hp⟩ := param_sound b hx
    apply ok.sum_ok
    intro i
    apply ok.mul_ok (ok.point_ok _)
    apply ok.mul_ok ((MasulloRH.horner_interval_and_derivative _).2 _ _
      (by simpa using ok.mul_ok (ok.point_ok (powerIndex i)) hu))
    unfold splitTerm
    rw [exp_power]
    apply ok.mul_ok hp
    have h := ok.mul_ok (ok.pow_ok hq (powerIndex i/2)) (ok.pow_ok hq (powerIndex i-powerIndex i/2))
    rw [←pow_add,Nat.add_sub_of_le (Nat.div_le_self _ _)] at h
    exact h
  · intro b z x hx hden
    rw [theta_zero]
    exact (single_error b x).trans ((MasulloRH.central_theta_interval_sound b z x hx).2.2 hden)
