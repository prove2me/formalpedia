-- Prove2me | solution 1 for LimitedSwitching.HighProb.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T12:13:35.725341+00:00
-- url     : https://prove2.me/submissions/6e3eb191-6863-48fc-9dec-aaac35874eb2

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace Queelius.MaxMoment
lemma exp_tail (x : ℝ) (hx : 0 ≤ x) :
    expMeasure 1 (Ioi x) = ENNReal.ofReal (Real.exp (-x)) := by
  have hc : expMeasure 1 (Iic x) = ENNReal.ofReal (1-Real.exp (-x)) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq one_pos,if_pos hx,one_mul]
  rw [← compl_Iic,measure_compl measurableSet_Iic (measure_ne_top _ _),measure_univ,hc]
  rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))]
  congr 1
  ring
lemma measurable_max {n : ℕ} [NeZero n] :
    Measurable (fun R : Fin n → ℝ => Finset.univ.sup' Finset.univ_nonempty R) := by
  have h := Finset.measurable_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun (i : Fin n) _ => (measurable_pi_apply i : Measurable (fun R : Fin n → ℝ => R i)))
  convert h using 1
  funext R
  exact (Finset.sup'_apply Finset.univ_nonempty (fun (i : Fin n) (R : Fin n → ℝ) => R i) R).symm
lemma max_tail {n : ℕ} [NeZero n] (x : ℝ) (hx : 0 ≤ x) :
    LimitedSwitching.HighProb.expLaw n {R | x < Finset.univ.sup' Finset.univ_nonempty R} ≤
      ENNReal.ofReal ((n:ℝ)*Real.exp (-x)) := by
  classical
  have he : {R : Fin n → ℝ | x < Finset.univ.sup' Finset.univ_nonempty R} =
      ⋃ i : Fin n, {R | x < R i} := by
    ext R
    simp [Finset.lt_sup'_iff]
  rw [he]
  apply (measure_iUnion_le _).trans
  have hm (i : Fin n) : LimitedSwitching.HighProb.expLaw n {R | x < R i} = ENNReal.ofReal (Real.exp (-x)) := by
    have h := (measurePreserving_eval (fun _ : Fin n => expMeasure 1) i).measure_preimage (measurableSet_Ioi : MeasurableSet (Ioi x)).nullMeasurableSet
    exact h.trans (exp_tail x hx)
  simp_rw [hm]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]


lemma exp_primitive (t y : ℝ) :
    (∫ s in 0..y, t*Real.exp (t*s)) = Real.exp (t*y)-1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Real.exp (t*s))
    (fun x _ => by simpa [mul_comm] using ((hasDerivAt_id x).const_mul t).exp)
    (show IntervalIntegrable (fun s : ℝ => t*Real.exp (t*s)) volume 0 y from
      (continuous_const.mul (continuous_const.mul continuous_id).rexp).intervalIntegrable _ _)
  simpa using h
lemma exp_tail_integral (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-s))*ENNReal.ofReal (t*Real.exp (t*s)) =
      ENNReal.ofReal (t/(1-t)) := by
  have he (s : ℝ) : ENNReal.ofReal (Real.exp (-s))*ENNReal.ofReal (t*Real.exp (t*s)) =
      ENNReal.ofReal (t*Real.exp ((t-1)*s)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_mul_Ioi (by linarith : t-1 < 0) 0).const_mul t)
    (by filter_upwards [] with s; positivity),integral_const_mul,integral_exp_mul_Ioi (by linarith : t-1 < 0) 0]
  congr 1
  simp only [mul_zero,Real.exp_zero]
  field_simp [ne_of_gt (sub_pos.mpr ht1),show t-1 ≠ 0 by linarith]
  ring
lemma moment_of_exp_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ s, 0 < s → μ {ω | s < Y ω} ≤ ENNReal.ofReal (Real.exp (-s)))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t*Y ω)) ∂μ ≤ ENNReal.ofReal (1/(1-t)) := by
  have hJ : (∫⁻ ω, ENNReal.ofReal (Real.exp (t*Y ω)-1) ∂μ) ≤ ENNReal.ofReal (t/(1-t)) := by
    have hl := lintegral_comp_eq_lintegral_meas_lt_mul μ
      (ae_of_all _ hY0) hY.aemeasurable
      (g := fun s : ℝ => t*Real.exp (t*s))
      (fun y _ => (continuous_const.mul (continuous_const.mul continuous_id).rexp).intervalIntegrable _ _)
      (by filter_upwards [] with s; positivity)
    simp_rw [exp_primitive] at hl
    rw [hl,← exp_tail_integral t ht0.le ht1]
    apply setLIntegral_mono' measurableSet_Ioi
    intro s hs
    gcongr
    exact htail s hs
  have he (ω : Ω) : ENNReal.ofReal (Real.exp (t*Y ω)) = 1+ENNReal.ofReal (Real.exp (t*Y ω)-1) := by
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) (by
      have h := Real.one_le_exp_iff.mpr (mul_nonneg ht0.le (hY0 ω)); linarith)]
    congr 1
    ring
  simp_rw [he]
  rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
  calc
    _ ≤ 1+ENNReal.ofReal (t/(1-t)) := add_le_add le_rfl hJ
    _ = ENNReal.ofReal (1/(1-t)) := by
      rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) (by positivity)]
      congr 1
      field_simp [ne_of_gt (sub_pos.mpr ht1)]
      ring

lemma shifted_max_tail {n : ℕ} [NeZero n] (s : ℝ) (hs : 0 < s) :
    LimitedSwitching.HighProb.expLaw n
      {R | s < max (Finset.univ.sup' Finset.univ_nonempty R-Real.log n) 0} ≤
      ENNReal.ofReal (Real.exp (-s)) := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have he : {R : Fin n → ℝ | s < max (Finset.univ.sup' Finset.univ_nonempty R-Real.log n) 0} =
      {R | Real.log n+s < Finset.univ.sup' Finset.univ_nonempty R} := by
    ext R
    simp only [Set.mem_setOf_eq,lt_max_iff]
    constructor
    · rintro (h|h) <;> linarith
    · intro h
      exact Or.inl (by linarith)
  rw [he]
  have hh := max_tail (n := n) (Real.log n+s) (by linarith)
  have hid : (n:ℝ)*Real.exp (-(Real.log n+s)) = Real.exp (-s) := by
    rw [neg_add,Real.exp_add,Real.exp_neg,Real.exp_log hn]
    field_simp
  simpa only [hid] using hh
lemma max_moment {n : ℕ} [NeZero n] (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ R, ENNReal.ofReal (Real.exp (t*Finset.univ.sup' Finset.univ_nonempty R))
      ∂LimitedSwitching.HighProb.expLaw n ≤ ENNReal.ofReal ((n:ℝ)^t/(1-t)) := by
  let Y := fun R : Fin n → ℝ => max (Finset.univ.sup' Finset.univ_nonempty R-Real.log n) 0
  have hY : Measurable Y := (measurable_max.sub measurable_const).max measurable_const
  have hY0 : ∀ R, 0 ≤ Y R := fun R => le_max_right _ _
  have hYtail : ∀ s, 0 < s → LimitedSwitching.HighProb.expLaw n {R | s < Y R} ≤ ENNReal.ofReal (Real.exp (-s)) :=
    shifted_max_tail
  have hm := moment_of_exp_tail (LimitedSwitching.HighProb.expLaw n) Y hY hY0 hYtail t ht0 ht1
  calc
    _ ≤ ∫⁻ R, ENNReal.ofReal (Real.exp (t*Real.log n)) * ENNReal.ofReal (Real.exp (t*Y R))
        ∂LimitedSwitching.HighProb.expLaw n := by
      apply lintegral_mono
      intro R
      change ENNReal.ofReal (Real.exp (t*Finset.univ.sup' Finset.univ_nonempty R)) ≤ ENNReal.ofReal (Real.exp (t*Real.log n))*ENNReal.ofReal (Real.exp (t*Y R))
      rw [← ENNReal.ofReal_mul (by positivity),← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hh : Finset.univ.sup' Finset.univ_nonempty R-Real.log n ≤ Y R := le_max_left _ _
      nlinarith
    _ = ENNReal.ofReal (Real.exp (t*Real.log n)) *
        ∫⁻ R, ENNReal.ofReal (Real.exp (t*Y R)) ∂LimitedSwitching.HighProb.expLaw n :=
      lintegral_const_mul _ ((measurable_const.mul hY).exp.ennreal_ofReal)
    _ ≤ ENNReal.ofReal (Real.exp (t*Real.log n)) * ENNReal.ofReal (1/(1-t)) := by gcongr
    _ = ENNReal.ofReal ((n:ℝ)^t/(1-t)) := by
      rw [← ENNReal.ofReal_mul (by positivity),Real.rpow_def_of_pos (by exact_mod_cast NeZero.pos n)]
      congr 1
      rw [mul_comm t (Real.log n)]
      ring
lemma atom_zero_control (t : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t*x)) ∂Measure.dirac 0 = 1 := by simp
lemma singleton_max_control (R : Fin 1 → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty R = R 0 := by simp
end Queelius.MaxMoment
open LimitedSwitching.HighProb in
 theorem solution {n : ℕ} [NeZero n] (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ R, ENNReal.ofReal (Real.exp (t * Finset.univ.sup' Finset.univ_nonempty R)) ∂(expLaw n)
      ≤ ENNReal.ofReal ((n : ℝ) ^ t / (1 - t)) := Queelius.MaxMoment.max_moment t ht0 ht1
