-- Prove2me | solution 1 for GittinsUCB.Patient.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:47:06.416221+00:00
-- url     : https://prove2.me/submissions/1e03e239-4bd3-400c-9543-68a062635eac

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsL4Aux

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


/-- Upper bound on the Mills ratio: `1 - Φ(c) ≤ (c²+2)/(c³+3c) φ(c)` for `c > 0`. -/
lemma tail_le_shenton (c : ℝ) (hc : 0 < c) :
    ∫ t in Set.Ioi c, stdPdf t ≤ (c ^ 2 + 2) / (c ^ 3 + 3 * c) * stdPdf c := by
  set F : ℝ → ℝ := fun t => -((t ^ 2 + 2) / (t ^ 3 + 3 * t) * stdPdf t) with hF
  set F' : ℝ → ℝ := fun t => stdPdf t + 6 * (stdPdf t / (t ^ 3 + 3 * t) ^ 2) with hF'
  have hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x := by
    intro x hx
    have hp : HasDerivAt (fun t : ℝ => t ^ 2 + 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const 2
    have hq : HasDerivAt (fun t : ℝ => t ^ 3 + 3 * t) (3 * x ^ 2 + 3) x :=
      ((hasDerivAt_pow 3 x).add ((hasDerivAt_id x).const_mul 3)).congr_deriv (by simp)
    have hne : x ^ 3 + 3 * x ≠ 0 := by positivity
    have h3 := ((hp.div hq hne).mul (hasDeriv_pdf x)).neg
    refine h3.congr_deriv ?_
    simp only [hF', Pi.div_apply]
    field_simp
    ring
  have hqpos : ∀ t, c ≤ t → c ^ 3 + 3 * c ≤ t ^ 3 + 3 * t := by
    intro t ht
    have : c ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hc.le ht 3
    linarith
  have hcont : ContinuousWithinAt F (Set.Ici c) c := by
    apply ContinuousAt.continuousWithinAt
    have hne : c ^ 3 + 3 * c ≠ 0 := by positivity
    rw [hF]
    exact ((((continuous_pow 2).add continuous_const).continuousAt.div
      ((continuous_pow 3).add (continuous_const.mul continuous_id)).continuousAt hne).mul
      continuous_pdf.continuousAt).neg
  have hint : IntegrableOn F' (Set.Ioi c) := by
    refine integrable_pdf.integrableOn.add (Integrable.const_mul ?_ 6)
    refine (integrable_pdf.integrableOn.const_mul ((c ^ 3 + 3 * c) ^ 2)⁻¹).mono' ?_ ?_
    · exact (continuous_pdf.measurable.div
        ((by fun_prop : Continuous fun t : ℝ => (t ^ 3 + 3 * t) ^ 2).measurable)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
      have ht' : c < t := ht
      have hφ := pdf_pos t
      have hq := hqpos t ht'.le
      have hc0 : 0 < c ^ 3 + 3 * c := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
      apply mul_le_mul_of_nonneg_right _ hφ.le
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hc0.le hq 2
  have hlim : Tendsto F atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ tendsto_pdf
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [hF, norm_neg, norm_mul, Real.norm_eq_abs (stdPdf t), abs_of_pos (pdf_pos t)]
    have hb : ‖(t ^ 2 + 2) / (t ^ 3 + 3 * t)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
      nlinarith
    have := pdf_pos t
    nlinarith
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (f := F) (f' := F') (a := c) (m := 0)
    hcont (fun x hx => hderiv x (lt_trans hc hx)) hint hlim
  have hmono : ∫ t in Set.Ioi c, stdPdf t ≤ ∫ t in Set.Ioi c, F' t := by
    refine setIntegral_mono_on integrable_pdf.integrableOn hint measurableSet_Ioi ?_
    intro t _
    simp only [hF']
    have : 0 ≤ stdPdf t / (t ^ 3 + 3 * t) ^ 2 := by have := pdf_pos t; positivity
    linarith
  rw [hI] at hmono
  simpa [hF] using hmono

/-- `E[(Z - c)⁺] = φ(c) - c (1 - Φ(c))` for a standard normal `Z`. -/
lemma G_eq (c : ℝ) : ∫ z, max (z - c) 0 ∂(gaussianReal 0 1) =
    stdPdf c - c * ∫ t in Set.Ioi c, stdPdf t := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, pdf_eq]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi c)]
  · have : ∫ z in Set.Ioi c, stdPdf z * max (z - c) 0 =
        ∫ z in Set.Ioi c, (z * stdPdf z - c * stdPdf z) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      have hz' : c < z := hz
      rw [max_eq_left (by linarith)]
      ring
    rw [this, integral_sub integrable_mul_pdf.integrableOn
      (integrable_pdf.integrableOn.const_mul c), integral_const_mul, integral_mul_pdf]
  · intro z hz
    have hz' : z ≤ c := not_lt.mp hz
    rw [max_eq_right (by linarith), mul_zero]

/-- Scaling: `E[(X - λ)⁺] = σ E[(Z - λ/σ)⁺]` for `X ∼ N(0, σ²)`. -/
lemma scale_eq (σ lam : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) =
      σ * ∫ z, max (z - lam / σ) 0 ∂(gaussianReal 0 1) := by
  have hm : (gaussianReal 0 1).map (σ * ·) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · exact NNReal.eq (by simp <;> rfl)
  rw [← hm, integral_map (f := fun x : ℝ => max (x - lam) 0) (measurable_const_mul σ).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => max (x - lam) 0).aestronglyMeasurable,
    ← integral_const_mul]
  congr 1
  funext z
  rw [mul_max_of_nonneg _ _ hσ.le, mul_zero, mul_sub, mul_div_cancel₀ _ hσ.ne']

end GittinsL4Aux

open GittinsL4Aux in
theorem solution (σ lam : ℝ) (hσ : 0 < σ) (hlam : 2 * σ ≤ lam) :
    σ ^ 4 / lam ^ 3 * stdPdf (lam / σ) ≤
      (∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) ∧
    (∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) ≤
      σ * stdPdf (lam / σ) := by
  rw [scale_eq σ lam hσ, G_eq]
  set c := lam / σ with hc
  have hc2 : 2 ≤ c := by rw [hc, le_div_iff₀ hσ]; linarith
  have hlamc : lam = σ * c := by rw [hc]; field_simp
  have hφ := pdf_pos c
  have hT0 : 0 ≤ ∫ t in Set.Ioi c, stdPdf t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => (pdf_pos t).le)
  have hT := tail_le_shenton c (by linarith)
  constructor
  · rw [hlamc]
    have hcT : c * ∫ t in Set.Ioi c, stdPdf t ≤ (c ^ 2 + 2) / (c ^ 2 + 3) * stdPdf c := by
      have e : c * ((c ^ 2 + 2) / (c ^ 3 + 3 * c) * stdPdf c) =
          (c ^ 2 + 2) / (c ^ 2 + 3) * stdPdf c := by
        field_simp
      rw [← e]
      exact mul_le_mul_of_nonneg_left hT (by linarith)
    have hG : stdPdf c / (c ^ 2 + 3) ≤ stdPdf c - c * ∫ t in Set.Ioi c, stdPdf t := by
      have e : stdPdf c / (c ^ 2 + 3) = stdPdf c - (c ^ 2 + 2) / (c ^ 2 + 3) * stdPdf c := by
        field_simp
        ring
      rw [e]; linarith
    have hc3 : stdPdf c / c ^ 3 ≤ stdPdf c / (c ^ 2 + 3) := by
      apply div_le_div_of_nonneg_left hφ.le (by positivity)
      nlinarith
    have e2 : σ ^ 4 / (σ * c) ^ 3 * stdPdf c = σ * (stdPdf c / c ^ 3) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left (hc3.trans hG) hσ.le
  · have : stdPdf c - c * ∫ t in Set.Ioi c, stdPdf t ≤ stdPdf c := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ c) hT0
      linarith
    exact mul_le_mul_of_nonneg_left this hσ.le
