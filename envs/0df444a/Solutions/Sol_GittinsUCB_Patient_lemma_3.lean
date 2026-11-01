-- Prove2me | solution 1 for GittinsUCB.Patient.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:44:19.013898+00:00
-- url     : https://prove2.me/submissions/47628c18-c2c3-4e45-bd1e-12c9121c506c

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsL3Aux

lemma pdf_eq (t : ℝ) : gaussianPDFReal 0 1 t = stdPdf t := by
  simp [gaussianPDFReal, stdPdf]
  ring

lemma pdf_pos (t : ℝ) : 0 < stdPdf t := by unfold stdPdf; positivity

lemma continuous_pdf : Continuous stdPdf := by
  unfold stdPdf; fun_prop

lemma integrable_pdf : Integrable stdPdf :=
  (integrable_gaussianPDFReal 0 1).congr (Eventually.of_forall pdf_eq)

lemma integrable_mul_pdf : Integrable (fun t => t * stdPdf t) := by
  have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).div_const
    (Real.sqrt (2 * Real.pi))
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only [stdPdf]
  have : -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 := by ring
  rw [this]
  ring

lemma cdf_eq (z : ℝ) : stdCdf z = 1 - ∫ t in Set.Ioi z, stdPdf t := by
  unfold stdCdf
  rw [cdf_eq_real]
  have h1 : (gaussianReal 0 1).real (Set.Ioi z) = ∫ t in Set.Ioi z, stdPdf t := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal]
    · simp_rw [pdf_eq]
    · exact setIntegral_nonneg measurableSet_Ioi (fun t _ => gaussianPDFReal_nonneg _ _ _)
  rw [← h1, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  ring

lemma hasDeriv_pdf (t : ℝ) : HasDerivAt stdPdf (-t * stdPdf t) t := by
  have h := (((hasDerivAt_pow 2 t).neg.div_const 2).exp).div_const (Real.sqrt (2 * Real.pi))
  refine h.congr_deriv ?_
  simp only [stdPdf]
  norm_num
  ring

lemma tendsto_pdf : Tendsto stdPdf atTop (nhds 0) := by
  unfold stdPdf
  have h : Tendsto (fun t : ℝ => -(t ^ 2) / 2) atTop atBot := by
    have : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    exact (tendsto_neg_atTop_atBot.comp this).congr (fun t => by simp [neg_div])
  simpa using (Real.tendsto_exp_atBot.comp h).div_const (Real.sqrt (2 * Real.pi))

lemma integral_mul_pdf (z : ℝ) : ∫ t in Set.Ioi z, t * stdPdf t = stdPdf z := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => -stdPdf t)
    (f' := fun t => t * stdPdf t) (a := z) (m := 0)
    (continuous_pdf.neg.continuousWithinAt)
    (fun x _ => by
      have := (hasDeriv_pdf x).neg
      simp only [neg_mul, neg_neg] at this
      exact this) integrable_mul_pdf.integrableOn
    (by simpa using tendsto_pdf.neg)
  simpa using this

/-- Gordon's upper bound: `1 - Φ(z) ≤ φ(z)/z`. -/
lemma tail_le (z : ℝ) (hz : 0 < z) : ∫ t in Set.Ioi z, stdPdf t ≤ stdPdf z / z := by
  have h : ∫ t in Set.Ioi z, stdPdf t ≤ ∫ t in Set.Ioi z, t * stdPdf t / z := by
    refine setIntegral_mono_on integrable_pdf.integrableOn
      (integrable_mul_pdf.div_const z).integrableOn measurableSet_Ioi ?_
    intro t ht
    have ht' : z < t := ht
    rw [le_div_iff₀ hz]
    have := pdf_pos t
    nlinarith
  rw [integral_div, integral_mul_pdf] at h
  exact h

/-- Gordon's lower bound: `z/(1+z²) φ(z) ≤ 1 - Φ(z)`. -/
lemma tail_ge (z : ℝ) : z / (1 + z ^ 2) * stdPdf z ≤ ∫ t in Set.Ioi z, stdPdf t := by
  set f : ℝ → ℝ := fun t => -(t / (1 + t ^ 2) * stdPdf t) with hf
  set f' : ℝ → ℝ := fun t => stdPdf t - 2 * (stdPdf t / (1 + t ^ 2) ^ 2) with hf'
  have hderiv : ∀ x, HasDerivAt f (f' x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have h2 := ((hasDerivAt_id x).div h1 hne).mul (hasDeriv_pdf x)
    have h3 := h2.neg
    refine h3.congr_deriv ?_
    simp only [hf', id, Pi.div_apply]
    field_simp
    ring
  have hcont : Continuous f := by
    rw [hf]
    exact ((continuous_id.div (continuous_const.add (continuous_pow 2))
      (fun t => by have : (0:ℝ) < 1 + t ^ 2 := by positivity
                   simpa using this.ne')).mul continuous_pdf).neg
  have hint : Integrable f' := by
    refine integrable_pdf.sub (Integrable.const_mul ?_ 2)
    refine integrable_pdf.mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact (continuous_pdf.div ((continuous_const.add (continuous_pow 2)).pow 2)
        (fun t => by have : (0:ℝ) < (1 + t ^ 2) ^ 2 := by positivity
                     simpa using this.ne')).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by have := pdf_pos t; positivity)]
      apply div_le_self (pdf_pos t).le
      have : 1 ≤ 1 + t ^ 2 := by nlinarith
      exact one_le_pow₀ this
  have hlim : Tendsto f atTop (nhds 0) := by
    have : Tendsto (fun t => ‖f t‖) atTop (nhds 0) := by
      refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) tendsto_pdf
      rw [hf, norm_neg, norm_mul, Real.norm_eq_abs (stdPdf t), abs_of_pos (pdf_pos t)]
      have hb : ‖t / (1 + t ^ 2)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + t ^ 2),
          div_le_one (by positivity)]
        have : |t| ^ 2 = t ^ 2 := sq_abs t
        nlinarith [abs_nonneg t]
      have := pdf_pos t
      nlinarith
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (f := f) (f' := f') (a := z) (m := 0)
    hcont.continuousWithinAt (fun x _ => hderiv x) hint.integrableOn hlim
  have hmono : ∫ t in Set.Ioi z, f' t ≤ ∫ t in Set.Ioi z, stdPdf t := by
    refine setIntegral_mono_on hint.integrableOn integrable_pdf.integrableOn
      measurableSet_Ioi ?_
    intro t _
    simp only [hf']
    have : 0 ≤ stdPdf t / (1 + t ^ 2) ^ 2 := by have := pdf_pos t; positivity
    linarith
  rw [hI] at hmono
  simpa [hf] using hmono

end GittinsL3Aux

open GittinsL3Aux in
theorem solution :
    Tendsto (fun γ : ℝ => stdQuantile γ -
      Real.sqrt (2 * Real.log (1 / (1 - γ))))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  have hu : Tendsto (fun γ : ℝ => Real.log (1 / (1 - γ)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) atTop := by
    have h1 : Tendsto (fun γ : ℝ => 1 - γ) (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun γ : ℝ => 1 - γ) (nhds 1) (nhds (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with γ hγ
        simp only [Set.mem_Iio] at hγ
        simp only [Set.mem_Ioi]; linarith
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    refine Real.tendsto_log_atTop.comp (h2.congr ?_)
    intro γ; simp
  have ha : Tendsto (fun γ : ℝ => Real.sqrt (2 * Real.log (1 / (1 - γ))))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) atTop :=
    Real.tendsto_sqrt_atTop.comp (hu.const_mul_atTop two_pos)
  rw [Metric.tendsto_nhds]
  intro δ0 hδ0
  set δ := min δ0 1 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδδ0 : δ < δ0 := by
    have : min δ0 1 ≤ δ0 := min_le_left _ _
    have : 0 < min δ0 1 := lt_min hδ0 one_pos
    linarith
  have hδ1 : δ ≤ 1 := by
    have : min δ0 1 ≤ 1 := min_le_right _ _
    linarith
  set K : ℝ := 2 * Real.sqrt (2 * Real.pi) with hKdef
  have hpi1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have := Real.pi_gt_three; linarith
  have hK0 : 0 < K := by positivity
  have hA : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ Real.log x ≤ δ / 2 * x ∧
      Real.log K + δ ^ 2 / 2 < δ / 2 * x := by
    refine (eventually_ge_atTop 2).and (Filter.Eventually.and ?_ ?_)
    · have := Real.isLittleO_log_id_atTop.def (c := δ / 2) (by positivity)
      filter_upwards [this, eventually_ge_atTop 1] with x hx hx1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
        id, abs_of_nonneg (by linarith)] at hx
      exact hx
    · have : Tendsto (fun x : ℝ => δ / 2 * x) atTop atTop :=
        tendsto_id.const_mul_atTop (by positivity)
      exact this.eventually_gt_atTop _
  filter_upwards [ha.eventually hA, Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)]
    with γ hA hγ
  obtain ⟨ha2, hloga, hKa⟩ := hA
  obtain ⟨hγ0, hγ1⟩ := hγ
  have h1γ : 0 < 1 - γ := by linarith
  set u := Real.log (1 / (1 - γ)) with hu_def
  set a := Real.sqrt (2 * u) with ha_def
  have hu0 : 0 ≤ u := by
    rw [hu_def]; apply Real.log_nonneg
    rw [le_div_iff₀ h1γ]; linarith
  have ha2u : a ^ 2 = 2 * u := by rw [ha_def]; exact Real.sq_sqrt (by linarith)
  have hexpu : Real.exp (-u) = 1 - γ := by
    rw [hu_def, Real.exp_neg, Real.exp_log (by positivity)]; simp
  -- `Φ(a) ≥ γ`
  have hup : γ ≤ stdCdf a := by
    rw [cdf_eq]
    have h1 := tail_le a (by linarith)
    have h2 : stdPdf a / a ≤ stdPdf a := div_le_self (pdf_pos a).le (by linarith)
    have h3 : stdPdf a ≤ Real.exp (-a ^ 2 / 2) := by
      unfold stdPdf; exact div_le_self (Real.exp_pos _).le hpi1
    have h4 : Real.exp (-a ^ 2 / 2) = 1 - γ := by
      rw [ha2u, ← hexpu]; congr 1; ring
    linarith
  -- `Φ(a - δ) < γ`
  set z := a - δ with hz
  have hz1 : 1 ≤ z := by linarith
  have hlow : stdCdf z < γ := by
    rw [cdf_eq]
    have hT := tail_ge z
    set E := Real.exp (a * δ - δ ^ 2 / 2) with hE
    have hKE : K * a < E := by
      rw [hE, ← Real.exp_log (by positivity : 0 < K * a)]
      apply Real.exp_lt_exp.mpr
      rw [Real.log_mul hK0.ne' (by linarith)]
      nlinarith
    have hφ : stdPdf z = Real.exp (-u) * E / Real.sqrt (2 * Real.pi) := by
      unfold stdPdf
      rw [hE, ← Real.exp_add]
      congr 2
      rw [hz]; nlinarith [ha2u]
    have hzz : 1 / (2 * z) ≤ z / (1 + z ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hza : 1 / (2 * a) ≤ 1 / (2 * z) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hφ0 : 0 < stdPdf z := pdf_pos z
    have step1 : 1 / (2 * a) * stdPdf z ≤ ∫ t in Set.Ioi z, stdPdf t := by
      have := mul_le_mul_of_nonneg_right (hza.trans hzz) hφ0.le
      linarith
    have step2 : 1 - γ < 1 / (2 * a) * stdPdf z := by
      rw [hφ, ← hexpu]
      have hsq : 0 < Real.sqrt (2 * Real.pi) := by linarith
      have he : 0 < Real.exp (-u) := Real.exp_pos _
      rw [show 1 / (2 * a) * (Real.exp (-u) * E / Real.sqrt (2 * Real.pi)) =
          Real.exp (-u) * (E / (K * a)) by rw [hKdef]; field_simp]
      have : 1 < E / (K * a) := by
        rw [one_lt_div (by positivity)]; exact hKE
      nlinarith
    linarith
  have hmono : Monotone stdCdf := fun x y h => (cdf (gaussianReal 0 1)).mono h
  have hbdd : BddBelow {w : ℝ | γ ≤ stdCdf w} := by
    refine ⟨z, fun w hw => ?_⟩
    by_contra hwz
    rw [not_le] at hwz
    have := hmono hwz.le
    simp only [Set.mem_setOf_eq] at hw
    linarith
  have hq1 : stdQuantile γ ≤ a := csInf_le hbdd hup
  have hq2 : z ≤ stdQuantile γ := by
    refine le_csInf ⟨a, hup⟩ (fun w hw => ?_)
    by_contra hwz
    rw [not_le] at hwz
    have := hmono hwz.le
    simp only [Set.mem_setOf_eq] at hw
    linarith
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith
