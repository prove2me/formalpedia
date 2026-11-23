-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_head_coefficient_enclosures
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:32:33.32738+00:00
-- url     : https://prove2.me/submissions/b7f12067-a45b-4da7-bacd-94c906530413
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_theorem_5_1
import Theorems.Thm_GrothendieckLB_Supplement_cqA_sextic_reduction
import Theorems.Thm_GrothendieckLB_Supplement_cq_sextic_moment_recurrence
import Theorems.Thm_GrothendieckLB_Supplement_cq_sextic_initial_integrals
import Theorems.Thm_GrothendieckLB_Supplement_cq_sextic_finite_head_arithmetic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib

open MeasureTheory Polynomial Real
open GrothendieckLB GrothendieckLB.Supplement

private noncomputable def density (s x : ℝ) : ℝ :=
  exp (-(x^2+(s*(x^3-3*x))^2)/2)

private noncomputable def moment (s : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, x^n * density s x

private theorem monomial_integrable (s : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x^n * density s x) := by
  have hg : Integrable fun x : ℝ => x^n * exp (-(1/2 : ℝ) * x^2) := by
    simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2:ℝ))
      (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (Nat.cast_nonneg n))
  apply hg.mono (by unfold density; fun_prop)
  filter_upwards with x
  simp only [density, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith only [sq_nonneg (s*(x^3-3*x))]

private theorem polynomial_moment (s : ℝ) (P : ℝ[X]) :
    ∫ x : ℝ, P.eval x * density s x = P.sum (fun n c => c*moment s n) := by
  simp_rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun n _ => (monomial_integrable s n).const_mul (P.coeff n))]
  simp only [integral_const_mul, moment]

private theorem odd_moment (s : ℝ) (n : ℕ) (hn : Odd n) : moment s n = 0 := by
  have hd (x : ℝ) : density s (-x) = density s x := by
    unfold density
    congr 1
    ring
  have h := integral_neg_eq_self (fun x : ℝ => x^n * density s x) volume
  simp only [hn.neg_pow, hd, neg_mul, integral_neg] at h
  unfold moment
  linarith only [h]

private theorem recovery (η s₃ s₅ : ℝ) :
    let s := η / Real.sqrt (6*(1+s₃^2+s₅^2))
    ∀ a b, a+b ≠ 0 → cqA η s₃ s₅ a b = cqHermiteFromMoments s (moment s) a b := by
  let s := η / Real.sqrt (6*(1+s₃^2+s₅^2))
  let H (n : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite n)
  have hH (n : ℕ) (x : ℝ) : ((hermite n).map (Int.castRingHom ℝ)).eval x = H n x := by
    rw [eval_map]
    rfl
  have h := cqA_sextic_reduction η s₃ s₅
  change (∀ a b, Real.pi * √((a+1).factorial:ℝ) * √(b.factorial:ℝ) * cqA η s₃ s₅ (a+1) b =
      ∫ x : ℝ, H a (-s*(x^3-3*x))*H b x*density s x) ∧
    (∀ b, Real.pi * √((b+1).factorial:ℝ) * cqA η s₃ s₅ 0 (b+1) =
      3*s * ∫ x : ℝ, (x^2-1)*H b x*density s x) at h
  change ∀ a b : ℕ, a+b ≠ 0 → cqA η s₃ s₅ a b = cqHermiteFromMoments s (moment s) a b
  intro a b hab
  rw [cqHermiteFromMoments, eq_div_iff (by positivity), mul_comm, ← polynomial_moment]
  cases a with
  | succ a =>
    simpa only [cqSexticPoly, eval_mul, eval_comp, eval_C, eval_sub, eval_pow, eval_X,
      hH, Nat.succ_eq_add_one] using h.1 a b
  | zero =>
    cases b with
    | zero => simp at hab
    | succ b =>
      simp only [cqSexticPoly, eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_one,
        hH, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, mul_one]
      rw [show (fun x : ℝ => 3*s*(x^2-1)*H b x*density s x) =
        (fun x => (3*s)*((x^2-1)*H b x*density s x)) by funext x; ring,
        integral_const_mul]
      exact h.2 b

theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ) / 10 ^ 20 ≤ taylorCoeff 1 H ∧
      ∀ j : ℕ, j < 125 → |taylorCoeff (2 * j + 3) H| ≤
          ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10 ^ 20 := by
  let s := 0.136419125 / Real.sqrt (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
  let M := moment s
  have hcoef (m : ℕ) (hm : 1 ≤ m) : taylorCoeff m (cqCorr 0.136419125 0.34101124 0.05276111) =
      cqHeadFromMoments M m := by
    rw [(theorem_5_1 0.136419125 0.34101124 0.05276111).2.1 m hm]
    unfold cqHeadFromMoments
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a+b=0
    · obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hab
      simp [Polynomial.coeff_one, Nat.ne_of_gt hm]
    · rw [recovery 0.136419125 0.34101124 0.05276111 a b hab]
  have hsq : s^2 = 0.136419125^2 / (6*(1+(0.34101124:ℝ)^2+0.05276111^2)) := by
    rw [show s = _ by rfl, div_pow, Real.sq_sqrt (by positivity)]
  have hcert := cq_sextic_finite_head_arithmetic M cq_sextic_initial_integrals
      (fun n _ hn => odd_moment s n hn)
      (fun n _ => by rw [← hsq]; exact cq_sextic_moment_recurrence s n)
  exact ⟨(hcoef 1 (by decide)).symm ▸ hcert.1,
    fun j hj => (hcoef (2*j+3) (by omega)).symm ▸ hcert.2 j hj⟩
