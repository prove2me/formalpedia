-- Prove2me | solution 1 for Helfgott.twisted_prime_LFunction_mellin
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T08:53:49.411604+00:00
-- url     : https://prove2.me/submissions/e0f6a934-7a45-4028-b86d-948b6882e9b8

import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators LSeries.notation

namespace Helfgott

lemma vertical_cpow_norm (x : ℝ) (hx : 0 < x) (σ t : ℝ) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma vertical_term_norm (c : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n‖ =
      ‖LSeries.term c (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

lemma positive_ratio_cpow_inverse (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((y / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hy.le hx.le, Complex.cpow_neg,
    Complex.cpow_neg]
  simp [div_eq_mul_inv, mul_comm]

lemma vertical_term_continuous (c : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hn0]
    exact continuous_const.div (by fun_prop) (fun _ => Complex.exp_ne_zero _)

lemma vertical_cpow_continuous (x : ℝ) (hx : 0 < x) (σ : ℝ) :
    Continuous (fun t : ℝ => (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.cpow_def_of_ne_zero hx0]
  fun_prop

lemma mellin_series_term_integrable (c : ℕ → ℂ) (σ x : ℝ) (hx : 0 < x)
    (f : ℝ → ℂ) (hF : Complex.VerticalIntegrable (mellin f) σ) (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ((vertical_term_continuous c σ n).mul (vertical_cpow_continuous x hx σ)).aestronglyMeasurable.mul hF.1
  apply (hF.norm.const_mul (‖LSeries.term c (σ : ℂ) n‖ * x ^ σ)).mono' hm
  filter_upwards [] with t
  rw [norm_mul, norm_mul, vertical_term_norm, vertical_cpow_norm x hx]

lemma mellin_series_norm_integrals_summable (c : ℕ → ℂ) (σ x : ℝ)
    (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x) (f : ℝ → ℂ) :
    Summable (fun n => ∫ t : ℝ,
      ‖LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
  simp_rw [norm_mul, vertical_term_norm, vertical_cpow_norm x hx,
    integral_const_mul]
  exact (hc.norm.mul_right (x ^ σ)).mul_right _

lemma mellin_series_integrable (c : ℕ → ℂ) (σ x : ℝ)
    (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x)
    (f : ℝ → ℂ) (hF : Complex.VerticalIntegrable (mellin f) σ) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hLm : AEStronglyMeasurable (fun t : ℝ =>
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    AEStronglyMeasurable.tsum (fun n => (vertical_term_continuous c σ n).aestronglyMeasurable)
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ((vertical_cpow_continuous x hx σ).aestronglyMeasurable.mul hF.1).mul hLm
  have hb (t : ℝ) : ‖LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∑' n, ‖LSeries.term c (σ : ℂ) n‖ := by
    have ht : Summable (fun n => ‖LSeries.term c
        ((σ : ℂ) + (t : ℂ) * Complex.I) n‖) :=
      hc.norm.congr (fun n => (vertical_term_norm c σ t n).symm)
    simpa only [LSeries, vertical_term_norm] using norm_tsum_le_tsum_norm ht
  apply (hF.norm.const_mul (x ^ σ * ∑' n, ‖LSeries.term c (σ : ℂ) n‖)).mono' hm
  filter_upwards [] with t
  rw [norm_mul, norm_mul, vertical_cpow_norm x hx]
  calc
    x ^ σ * ‖mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        ‖LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      x ^ σ * ‖mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (∑' n, ‖LSeries.term c (σ : ℂ) n‖) := by
      gcongr
      exact hb t
    _ = _ := by ring

theorem mellin_weighted_series_hasSum (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (σ x : ℝ) (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    HasSum (fun n => c n * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hi : ∀ n, Integrable (F n) := mellin_series_term_integrable c σ x hx f hF
  have hs : Summable (fun n => ∫ t, ‖F n t‖) :=
    mellin_series_norm_integrals_summable c σ x hc hx f
  have hterm (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t, F n t) =
      c n * f ((n : ℝ) / x) := by
    by_cases hn : n = 0
    · subst n
      simp [F, hc0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnratio : 0 < (n : ℝ) / x := div_pos hnpos hx
      have hinv := mellinInv_mellin_eq σ f hnratio hf hF
        (hcont.continuousAt (Ioi_mem_nhds hnratio))
      rw [← hinv]
      simp only [mellinInv, smul_eq_mul, Complex.real_smul]
      rw [← mul_assoc, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [F]
      rw [LSeries.term_of_ne_zero hn,
        positive_ratio_cpow_inverse x (n : ℝ) hx hnpos]
      push_cast
      ring
  have hsum := (hasSum_integral_of_summable_integral_norm hi hs).const_smul
    (1 / (2 * Real.pi) : ℝ)
  simp_rw [hterm] at hsum
  have heq : (∫ t : ℝ, ∑' n, F n t) =
      ∫ t : ℝ, (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [F]
    rw [tsum_mul_right, tsum_mul_right]
    unfold LSeries
    ring
  rw [heq] at hsum
  exact hsum

theorem twisted_prime_mellin_hasSum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv (LSeries (fun n : ℕ => χ n)) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          LSeries (fun n : ℕ => χ n) ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hσc : 1 < (σ : ℂ).re := by simpa using hσ
  have hc := χ.LSeriesSummable_twist_vonMangoldt hσc
  have hs := mellin_weighted_series_hasSum
    (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp)
    σ x hc hx f hf hF hcont
  convert hs using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have he := χ.LSeries_twist_vonMangoldt_eq ht
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    rfl
  rw [hec] at he
  exact congrArg
    (fun z : ℂ => (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) * z)
    he.symm

lemma twisted_prime_LFunction_identity (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv χ.LFunction s / χ.LFunction s := by
  rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
  have he := χ.LSeries_twist_vonMangoldt_eq hs
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    rfl
  rw [hec] at he
  exact he

theorem twisted_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
        χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
          χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hσc : 1 < (σ : ℂ).re := by simpa using hσ
  have hc := χ.LSeriesSummable_twist_vonMangoldt hσc
  have he (t : ℝ) := twisted_prime_LFunction_identity q χ
    ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  have hi := mellin_series_integrable
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ x hc hx f hF
  have hs := mellin_weighted_series_hasSum
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp)
    σ x hc hx f hf hF hcont
  simp_rw [he] at hi hs
  exact ⟨hi, hs⟩


end Helfgott

open MeasureTheory Set

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
        χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
          χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) := Helfgott.twisted_prime_LFunction_mellin q χ σ x hσ hx f hf hF hcont

#print axioms solution
