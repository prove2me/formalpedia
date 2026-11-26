-- Prove2me | solution 1 for MasulloRH.gaussian_window_translate_mixture_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:17:11.436182+00:00
-- url     : https://prove2.me/submissions/9f1d7528-323f-4f3e-b3cb-136f205afe97

import Definitions.Def_MasulloRH_GaussianMixtureWindows
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Real MasulloRH.GaussianApproximation

/-- A positive finite mixture of translated residuals has a uniform energy bound on every window contained in the scale-two witness window. The loss is a finite exponential moment of the shifts. -/
theorem solution {m : ℕ} (a y : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (D R : ℝ → ℂ)
    (c b : ℝ) (hl : 25/48 ≤ c-b) (hr : c+b ≤ 47/48)
    (hD : Integrable (fun x : ℝ => exp (2*c*x+2*b*|x|)*‖D x‖^2))
    (hR : Integrable (fun x : ℝ => exp (2*(3/4)*x+2*(11/48)*|x|)*‖R x‖^2)) :
    energy c b (fun x => D x + ∑ i, (a i : ℂ)*R (x-y i)) ≤
      2*energy c b D + 2*(∑ i, a i)*(∑ i, a i*exp (2*max 0 (y i)))*energy (3/4) (11/48) R := by
  let w (x : ℝ) := exp (2*c*x+2*b*|x|)
  let W (x : ℝ) := exp (2*(3/4)*x+2*(11/48)*|x|)
  let S := ∑ i, a i
  let M := fun x : ℝ => ∑ i, (a i : ℂ)*R (x-y i)
  let P := fun (i : Fin m) (x : ℝ) => (a i*exp (2*max 0 (y i)))*(W (x-y i)*‖R (x-y i)‖^2)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => ha i)
  have shift (x t : ℝ) : w x ≤ exp (2*max 0 t)*W (x-t) := by
    have within : w x ≤ W x := by
      apply exp_le_exp.2
      rcases le_total 0 x with hx|hx
      · rw [abs_of_nonneg hx];nlinarith [mul_nonneg (sub_nonneg.mpr hr) hx]
      · rw [abs_of_nonpos hx];nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hx]
    apply within.trans;dsimp only [W];rw [← exp_add];apply exp_le_exp.2
    have ht := abs_add_le (x-t) t;rw [sub_add_cancel] at ht
    rcases le_total 0 t with hp|hp
    · rw [max_eq_right hp,abs_of_nonneg hp] at *;linarith
    · rw [max_eq_left hp,abs_of_nonpos hp] at *;linarith
  have mean (x : ℝ) : ‖M x‖^2 ≤ S*(∑ i, a i*‖R (x-y i)‖^2) := by
    have triangle := norm_sum_le (s:=Finset.univ) (f:=fun i : Fin m => (a i : ℂ)*R (x-y i))
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha _)] at triangle
    have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (r:=fun i => a i*‖R (x-y i)‖)
      (f:=a) (g:=fun i => a i*‖R (x-y i)‖^2) Finset.univ (fun i _ => ha i)
      (fun i _ => mul_nonneg (ha i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))
    exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (norm_nonneg _)))).2 triangle).trans hs
  have pInt (i : Fin m) : Integrable (P i) := (hR.comp_sub_right (y i)).const_mul _
  have pval (i : Fin m) : (∫ x : ℝ, P i x)=(a i*exp (2*max 0 (y i)))*energy (3/4) (11/48) R := by
    dsimp only [P];rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun x => W x*‖R x‖^2) (y i)
  have sumInt := integrable_finsetSum Finset.univ (fun i _ => pInt i)
  have fI : Integrable (fun x => 2*(w x*‖D x‖^2)) := hD.const_mul _
  have gI : Integrable (fun x => (2*S)*(∑ i, P i x)) := sumInt.const_mul _
  have upper : energy c b (fun x => D x+M x) ≤
      ∫ x : ℝ, 2*(w x*‖D x‖^2)+(2*S)*(∑ i, P i x) := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun _ => mul_nonneg (exp_nonneg _) (sq_nonneg _))) (fI.add gI)
    apply ae_of_all;intro x
    change w x*‖D x+M x‖^2 ≤ 2*(w x*‖D x‖^2)+(2*S)*(∑ i, P i x)
    have tri := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 (norm_add_le (D x) (M x))
    have two : ‖D x+M x‖^2 ≤ 2*‖D x‖^2+2*(S*∑ i, a i*‖R (x-y i)‖^2) := by
      nlinarith only [tri,mean x,sq_nonneg (‖D x‖-‖M x‖)]
    have weight : w x*(∑ i, a i*‖R (x-y i)‖^2) ≤ ∑ i, P i x := by
      rw [Finset.mul_sum];apply Finset.sum_le_sum;intro i hi
      have e := mul_le_mul_of_nonneg_right (shift x (y i)) (mul_nonneg (ha i) (sq_nonneg ‖R (x-y i)‖))
      dsimp only [P];nlinarith only [e]
    nlinarith only [mul_le_mul_of_nonneg_left two (exp_nonneg _ : 0 ≤ w x),mul_le_mul_of_nonneg_left weight hS]
  rw [integral_add fI gI,integral_const_mul,integral_const_mul,integral_finsetSum _ (fun i _ => pInt i)] at upper
  have id : (∑ i, ∫ x : ℝ, P i x)=(∑ i, a i*exp (2*max 0 (y i)))*energy (3/4) (11/48) R := by
    rw [Finset.sum_mul];exact Finset.sum_congr rfl (fun i _ => pval i)
  rw [id] at upper
  change energy c b (fun x => D x+M x) ≤ 2*energy c b D + 2*S*(∑ i, a i*exp (2*max 0 (y i)))*energy (3/4) (11/48) R
  unfold energy at upper ⊢;dsimp only [w] at upper;linarith
