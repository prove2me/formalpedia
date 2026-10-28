-- Prove2me | solution 1 for LimitedSwitching.HighProb.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T11:31:47.64712+00:00
-- url     : https://prove2.me/submissions/685ad4f7-f530-4618-b91a-16db17a8a06c

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace MaxTail
lemma exp_moment (t : ℝ) (ht : t < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t*x)) ∂expMeasure 1 = ENNReal.ofReal (1/(1-t)) := by
  change (∫⁻ x, ENNReal.ofReal (Real.exp (t*x)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (by unfold exponentialPDF; fun_prop) (by fun_prop)]
  have hp (x : ℝ) : exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t*x)) =
      ENNReal.ofReal (1/(1-t)) * exponentialPDF (1-t) x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [one_mul, ← Real.exp_add]
      have he : -(1*x)+t*x = -((1-t)*x) := by ring
      rw [he]
      field_simp [ne_of_gt (sub_pos.mpr ht)]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx)]
      simp
  change (∫⁻ x, exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t*x))) = _
  simp_rw [hp]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop), lintegral_exponentialPDF_eq_one (by linarith), mul_one]

lemma exp_max_le_sum {n : ℕ} [NeZero n] (t : ℝ) (ht : 0 ≤ t) (R : Fin n → ℝ) :
    Real.exp (t * Finset.univ.sup' Finset.univ_nonempty R) ≤
      ∑ i, Real.exp (t * R i) := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty R
  rw [he]
  exact Finset.single_le_sum (f := fun j => Real.exp (t * R j)) (fun j _ => (Real.exp_pos _).le) hi


lemma moment_max {n : ℕ} [NeZero n] (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    ∫⁻ R, ENNReal.ofReal (Real.exp (t * Finset.univ.sup' Finset.univ_nonempty R))
      ∂LimitedSwitching.HighProb.expLaw n ≤ ENNReal.ofReal ((n:ℝ)/(1-t)) := by
  classical
  calc
    _ ≤ ∫⁻ R : Fin n → ℝ, ∑ i, ENNReal.ofReal (Real.exp (t*R i))
        ∂Measure.pi (fun _ => expMeasure 1) := by
      apply lintegral_mono
      intro R
      exact (ENNReal.ofReal_le_ofReal (exp_max_le_sum t ht R)).trans_eq
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le))
    _ = ∑ i : Fin n, ∫⁻ R : Fin n → ℝ, ENNReal.ofReal (Real.exp (t*R i))
        ∂Measure.pi (fun _ => expMeasure 1) := lintegral_finsetSum _ (by intros; fun_prop)
    _ = ∑ _i : Fin n, ENNReal.ofReal (1/(1-t)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(measurePreserving_eval (fun _ : Fin n => expMeasure 1) i).lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (Real.exp (t*x))) (by fun_prop), exp_moment t ht1]
    _ = ENNReal.ofReal ((n:ℝ)/(1-t)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

lemma measurable_max {n : ℕ} [NeZero n] :
    Measurable (fun R : Fin n → ℝ => Finset.univ.sup' Finset.univ_nonempty R) :=
  by
    have h := Finset.measurable_sup' (s := Finset.univ) Finset.univ_nonempty
      (fun (i : Fin n) _ => (measurable_pi_apply i : Measurable (fun R : Fin n → ℝ => R i)))
    convert h using 1
    funext R
    exact (Finset.sup'_apply Finset.univ_nonempty (fun (i : Fin n) (R : Fin n → ℝ) => R i) R).symm


lemma moment_sum {N n : ℕ} [NeZero n] (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    ∫⁻ R, ENNReal.ofReal (Real.exp (t * ∑ e : Fin N,
      Finset.univ.sup' Finset.univ_nonempty (R e)))
      ∂Measure.pi (fun _ : Fin N => LimitedSwitching.HighProb.expLaw n) ≤
      ENNReal.ofReal (((n:ℝ)/(1-t))^N) := by
  classical
  have hm : Measurable (fun R : Fin n → ℝ => ENNReal.ofReal
      (Real.exp (t * Finset.univ.sup' Finset.univ_nonempty R))) :=
    (measurable_const.mul measurable_max).exp.ennreal_ofReal
  have hp (R : Fin N → Fin n → ℝ) : ENNReal.ofReal (Real.exp
      (t * ∑ e, Finset.univ.sup' Finset.univ_nonempty (R e))) =
      ∏ e, ENNReal.ofReal (Real.exp (t * Finset.univ.sup' Finset.univ_nonempty (R e))) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)
  simp_rw [hp]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
    (iIndepFun_pi (fun _ => hm.aemeasurable)) (fun i => hm.comp (measurable_pi_apply i))]
  calc
    _ ≤ ∏ _e : Fin N, ENNReal.ofReal ((n:ℝ)/(1-t)) := by
      apply Finset.prod_le_prod (by intros; positivity)
      intro e _
      rw [← lintegral_map hm (measurable_pi_apply e),
        (measurePreserving_eval (fun _ : Fin N => LimitedSwitching.HighProb.expLaw n) e).map_eq]
      exact moment_max t ht ht1
    _ = ENNReal.ofReal (((n:ℝ)/(1-t))^N) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [ENNReal.ofReal_pow (by positivity)]

lemma tail_from_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (t a B : ℝ) (ht : 0 < t) (hB : 0 ≤ B)
    (hM : ∫⁻ x, ENNReal.ofReal (Real.exp (t * X x)) ∂μ ≤ ENNReal.ofReal B) :
    μ {x | a < X x} ≤ ENNReal.ofReal (B / Real.exp (t*a)) := by
  calc
    _ ≤ μ {x | ENNReal.ofReal (Real.exp (t*a)) ≤ ENNReal.ofReal (Real.exp (t*X x))} := by
      apply measure_mono
      intro x hx
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.le ht.le))
    _ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (t*X x)) ∂μ) / ENNReal.ofReal (Real.exp (t*a)) :=
      meas_ge_le_lintegral_div ((measurable_const.mul hX).exp.ennreal_ofReal.aemeasurable)
        (by simp [ENNReal.ofReal_eq_zero, (Real.exp_pos _).not_ge]) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (Real.exp (t*a)) := by gcongr
    _ = _ := (ENNReal.ofReal_div_of_pos (Real.exp_pos _)).symm

lemma numerical_tail {N n : ℕ} (hn : 2 ≤ n) :
    ((n:ℝ)/(1-(3/4:ℝ)))^N / Real.exp ((3/4:ℝ)*(6*(N:ℝ)*Real.log n)) ≤
      Real.exp (-(N:ℝ)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlog4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hlogn : Real.log (4*(n:ℝ)) = 2*Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) hn0.ne', hlog4]
  have hc : Real.log (4*(n:ℝ)) - (9/2:ℝ)*Real.log n ≤ -1 := by
    rw [hlogn]
    linarith [Real.log_two_gt_d9]
  have he : Real.exp (Real.log (4*(n:ℝ))) = 4*n := Real.exp_log (by positivity)
  have hd : (n:ℝ)/(1-(3/4:ℝ)) = 4*n := by ring
  rw [hd, ← he, ← Real.exp_nat_mul, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  calc
    _ = (N:ℝ)*(Real.log (4*(n:ℝ))-(9/2:ℝ)*Real.log n) := by ring
    _ ≤ (N:ℝ)*(-1) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring
lemma moment_zero_control :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((0:ℝ)*x)) ∂expMeasure 1 = 1 := by
  simpa using exp_moment 0 (by norm_num)
lemma moment_three_quarters_control :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((3/4:ℝ)*x)) ∂expMeasure 1 = 4 := by
  rw [exp_moment (3/4) (by norm_num)]
  norm_num
lemma constant_rows_control (N n : ℕ) [NeZero n] (c : ℝ) :
    (∑ _e : Fin N, Finset.univ.sup' Finset.univ_nonempty (fun _i : Fin n => c)) = (N:ℝ)*c := by
  simp
end MaxTail

open LimitedSwitching.HighProb in
theorem solution {N n : ℕ} [NeZero n] (hN : 2 ≤ N) (hn : 2 ≤ n) :
    (Measure.pi (fun _ : Fin N => expLaw n))
        {R | 6 * (N : ℝ) * Real.log n < ∑ e, Finset.univ.sup' Finset.univ_nonempty (R e)}
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ))) := by
  have hm : Measurable (fun R : Fin N → Fin n → ℝ =>
      ∑ e, Finset.univ.sup' Finset.univ_nonempty (R e)) := by
    exact Finset.measurable_sum _ (fun e _ => MaxTail.measurable_max.comp (measurable_pi_apply e))
  exact (MaxTail.tail_from_moment _ _ hm (3/4) _ _ (by norm_num) (by positivity)
    (MaxTail.moment_sum _ (by norm_num) (by norm_num))).trans
      (ENNReal.ofReal_le_ofReal (MaxTail.numerical_tail hn))
