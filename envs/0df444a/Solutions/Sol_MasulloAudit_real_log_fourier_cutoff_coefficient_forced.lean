-- Prove2me | solution 1 for MasulloAudit.real_log_fourier_cutoff_coefficient_forced
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:58:04.815914+00:00
-- url     : https://prove2.me/submissions/d2bc4ec5-152b-4ef3-b048-d772b73aadd5

import Mathlib

/-!
# Real-place finite part in logarithmic norm coordinates

For the positive real branch in Masullo (13.3.1.4), the kernel in
`x = log |g|` has singular term `1 / |x|`. With the symmetric log cutoff
`|x| > δ`, the counterterm for the pole is `2 h(0) log δ`.
Rescaling the test by `x ↦ x / ε` changes the finite part by
`2 h(0) log ε`. The absolute factor of two comes from the two sides
of the singularity in the positive real branch.
-/

open Filter MeasureTheory Set
open scoped Interval Topology

namespace MasulloAudit

private def outside (δ : ℝ) : Set ℝ := {x | δ < |x|}

private lemma measurableSet_outside (δ : ℝ) : MeasurableSet (outside δ) :=
  isOpen_lt continuous_const continuous_abs |>.measurableSet

/-- Symmetric cutoff of the real pole together with its finite-part counterterm. -/
noncomputable def cutoffRealPole (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in outside δ, h x / |x|) + 2 * h 0 * Real.log δ

/-- Exact scale identity at every positive cutoff. -/
theorem cutoffRealPole_scale (h : ℝ → ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    cutoffRealPole (fun x ↦ h (x / ε)) δ =
      cutoffRealPole h (δ / ε) + 2 * h 0 * Real.log ε := by
  have hcut : (∫ x in outside δ, h (x / ε) / |x|) = ∫ y in outside (δ / ε), h y / |y| := by
    rw [← integral_indicator (measurableSet_outside δ),
      ← integral_indicator (measurableSet_outside (δ / ε))]
    have hfun : (outside δ).indicator (fun x ↦ h (x / ε) / |x|) =
        fun x ↦ ε⁻¹ * (outside (δ / ε)).indicator (fun y ↦ h y / |y|) (x / ε) := by
      funext x
      have hmem : x / ε ∈ outside (δ / ε) ↔ x ∈ outside δ := by
        simp only [outside, mem_ofPred_eq, abs_div, abs_of_pos hε]
        exact div_lt_div_iff_of_pos_right hε
      by_cases hx : x ∈ outside δ
      · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx), abs_div, abs_of_pos hε]
        have hx0 : |x| ≠ 0 := (hδ.trans hx).ne'
        field_simp
      · rw [indicator_of_notMem hx, indicator_of_notMem (hmem.not.mpr hx), mul_zero]
    rw [hfun, integral_const_mul, Measure.integral_comp_div, abs_of_pos hε, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
  rw [cutoffRealPole, cutoffRealPole, zero_div, hcut, Real.log_div hδ.ne' hε.ne']
  ring

private def annulus (δ : ℝ) : Set ℝ := {x | δ < |x| ∧ |x| ≤ 1}

private lemma annulus_eq {δ : ℝ} (hδ : 0 < δ) :
    annulus δ = Ico (-1) (-δ) ∪ Ioc δ 1 := by
  ext x
  change (δ < |x| ∧ |x| ≤ 1) ↔ (-1 ≤ x ∧ x < -δ) ∨ (δ < x ∧ x ≤ 1)
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    constructor
    · exact Or.inr
    · rintro (hh | hh)
      · linarith [hh.2]
      · exact hh
  · rw [abs_of_nonpos hx.le]
    constructor
    · intro hh
      exact Or.inl ⟨by linarith [hh.2], by linarith [hh.1]⟩
    · rintro (hh | hh)
      · exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
      · linarith [hh.1]

private lemma invAbs_integrable_interval {a b : ℝ} (hz : (0 : ℝ) ∉ uIcc a b) :
    IntervalIntegrable (fun x : ℝ ↦ |x|⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine continuous_abs.continuousOn.inv₀ fun x hx ↦ ?_
  exact abs_ne_zero.mpr (fun he ↦ hz (he ▸ hx))

private lemma invAbs_integrable_annulus {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (annulus δ) := by
  have hn : (-1 : ℝ) ≤ -δ := by linarith
  have hi₁ := invAbs_integrable_interval (a := -1) (b := -δ) (by
    rw [uIcc_of_le hn]; intro hz; linarith [hz.2])
  have hi₂ := invAbs_integrable_interval (a := δ) (b := 1) (by
    rw [uIcc_of_le hδ₁]; intro hz; linarith [hz.1])
  rw [annulus_eq hδ]
  have hi₁' : IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (Ioc (-1) (-δ)) := hi₁.1
  have he : IntegrableOn (fun x : ℝ ↦ |x|⁻¹) (Ico (-1) (-δ)) := by
    simpa only [IntegrableOn, Measure.restrict_congr_set (μ := volume) Ico_ae_eq_Ioc] using hi₁'
  exact he.union hi₂.1

private lemma integral_invAbs_annulus {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (∫ x in annulus δ, |x|⁻¹) = -2 * Real.log δ := by
  have hn : (-1 : ℝ) ≤ -δ := by linarith
  have ha := invAbs_integrable_annulus hδ hδ₁
  have hs : Disjoint (Ico (-1) (-δ)) (Ioc δ 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1]
  rw [annulus_eq hδ, setIntegral_union hs measurableSet_Ioc
    (ha.mono_set (annulus_eq hδ ▸ subset_union_left))
    (ha.mono_set (annulus_eq hδ ▸ subset_union_right)),
    setIntegral_congr_set Ico_ae_eq_Ioc, ← intervalIntegral.integral_of_le hn,
    ← intervalIntegral.integral_of_le hδ₁]
  have hleft : (∫ x in (-1 : ℝ)..(-δ), |x|⁻¹) = - Real.log δ := by
    calc
      _ = ∫ x in (-1 : ℝ)..(-δ), -x⁻¹ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hn] at hx
        change |x|⁻¹ = -x⁻¹
        rw [abs_of_nonpos (by linarith [hx.2]), inv_neg]
      _ = _ := by
        rw [intervalIntegral.integral_neg, integral_inv_of_neg (by norm_num) (by linarith)]
        simp
  have hright : (∫ x in δ..1, |x|⁻¹) = - Real.log δ := by
    calc
      _ = ∫ x in δ..1, x⁻¹ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hδ₁] at hx
        change |x|⁻¹ = x⁻¹
        rw [abs_of_nonneg (hδ.le.trans hx.1)]
      _ = _ := by rw [integral_inv_of_pos hδ zero_lt_one, one_div, Real.log_inv]
  rw [hleft, hright]
  ring

/-- Subtract the value at the pole on the unit interval before integrating. -/
noncomputable def subtractedRealPole (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (h x - (Icc (-1 : ℝ) 1).indicator (fun _ ↦ h 0) x) / |x|

private lemma cutoffRealPole_eq_integral {h : ℝ → ℝ} (hg : Integrable (subtractedRealPole h))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    cutoffRealPole h δ = ∫ x in outside δ, subtractedRealPole h x := by
  have ha : MeasurableSet (annulus δ) := by rw [annulus_eq hδ]; exact measurableSet_Ico.union measurableSet_Ioc
  have hS := measurableSet_outside δ
  have hfun : (outside δ).indicator (fun x ↦ h x / |x|) = fun x ↦
      (outside δ).indicator (subtractedRealPole h) x +
      h 0 * (annulus δ).indicator (fun x : ℝ ↦ |x|⁻¹) x := by
    funext x
    by_cases hx : x ∈ outside δ
    · rcases le_or_gt |x| 1 with hx₁ | hx₁
      · have hI : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx₁
        have hA : x ∈ annulus δ := ⟨hx, hx₁⟩
        rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hA, subtractedRealPole,
          indicator_of_mem hI]
        rw [sub_div, div_eq_mul_inv (h 0), sub_add_cancel]
      · have hI : x ∉ Icc (-1 : ℝ) 1 := fun h ↦ hx₁.not_ge (abs_le.mpr h)
        have hA : x ∉ annulus δ := fun h ↦ hx₁.not_ge h.2
        rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_notMem hA, mul_zero, add_zero,
          subtractedRealPole, indicator_of_notMem hI, sub_zero]
    · have hA : x ∉ annulus δ := fun h ↦ hx h.1
      rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hA, mul_zero, zero_add]
  rw [cutoffRealPole, ← integral_indicator hS, hfun,
    integral_add (hg.indicator hS) ((invAbs_integrable_annulus hδ hδ₁).integrable_indicator ha |>.const_mul (h 0)),
    integral_indicator hS, integral_const_mul, integral_indicator ha, integral_invAbs_annulus hδ hδ₁]
  ring

private lemma tendsto_integral_outside {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun δ ↦ ∫ x in outside δ, f x) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x)) := by
  have hi : Tendsto (fun δ ↦ ∫ x, (outside δ).indicator (f) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    · exact Eventually.of_forall (fun δ ↦ hf.aestronglyMeasurable.indicator (measurableSet_outside δ))
    · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall (fun x ↦ by
        by_cases hx : x ∈ outside δ
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _))
    · exact hf.norm
    · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
      filter_upwards [hne] with x hx
      have he : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < |x| :=
        (gt_mem_nhds (abs_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [he] with δ hδ
      exact (indicator_of_mem (show x ∈ outside δ from hδ) _).symm
  simpa only [integral_indicator (measurableSet_outside _)] using hi

/-- The normalized cutoff integral converges to the integral of the subtracted kernel. -/
theorem cutoffRealPole_tendsto {h : ℝ → ℝ} (hg : Integrable (subtractedRealPole h)) :
    Tendsto (cutoffRealPole h) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, subtractedRealPole h x)) := by
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ 1 := by
    have h0 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have h1 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < 1 :=
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [h0, h1] with δ hδ hδ₁ using ⟨hδ, hδ₁.le⟩
  have hi := tendsto_integral_outside hg
  refine hi.congr' ?_
  filter_upwards [hall] with δ hδ
  exact (cutoffRealPole_eq_integral hg hδ.1 hδ.2).symm

/-- Scaling the test shifts the finite part by exactly `2 * h 0 * log ε`. -/
theorem cutoffRealPole_scaled_tendsto {h : ℝ → ℝ} (hg : Integrable (subtractedRealPole h))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (cutoffRealPole (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x, subtractedRealPole h x) + 2 * h 0 * Real.log ε)) := by
  have hdiv : Tendsto (fun δ : ℝ ↦ δ / ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const ε).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with δ hδ
      exact div_pos hδ hε
  have hlim := ((cutoffRealPole_tendsto hg).comp hdiv).add_const (2 * h 0 * Real.log ε)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with δ hδ
  exact (cutoffRealPole_scale h hε hδ).symm

end MasulloAudit

/-!
# Additive Fourier scaling in the real principal value

Masullo defines the distribution in Appendix B from the real logarithm
and the self-dual additive Haar measure. The scale law forces a coefficient
of one in its logarithmic counterterm. The cutoff printed in (B.4.3.13)
has coefficient two. Compare Connes, Appendix II, equations (30) and (34).
-/

open Filter MeasureTheory Set FourierTransform
open scoped SchwartzMap FourierTransform Topology Interval

namespace MasulloAudit

/-- The distribution obtained by Fourier transforming the real logarithm
under the usual Lebesgue self-dual normalization. -/
noncomputable def realLogFourier (f : ℝ → ℂ) : ℂ :=
  ∫ ξ : ℝ, (Real.log |ξ| : ℂ) * 𝓕 f ξ

private lemma integrable_log_mul_schwartz (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ (Real.log |x| : ℂ) * g x) := by
  let K := Icc (-1 : ℝ) 1
  let f (x : ℝ) := (Real.log |x| : ℂ) * g x
  have hf : Measurable f := by
    unfold f
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_abs)).mul
      g.continuous.measurable
  have hLog : IntegrableOn (fun x : ℝ ↦ Real.log |x|) K := by
    simp only [Real.log_abs, K]
    have h : IntegrableOn (fun x : ℝ ↦ Real.log x) (Ioc (-1 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).1
    simpa only [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] using h
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hNear : IntegrableOn f K := by
    refine (hLog.norm.const_mul C).mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with x
    dsimp only [f]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g x) (abs_nonneg _)
  have hFar : IntegrableOn f Kᶜ := by
    have hI := (g.integrable_pow_mul volume 1).integrableOn (s := Kᶜ)
    refine hI.mono' hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : 1 < |x| := lt_of_not_ge fun he ↦ hx (abs_le.mp he)
    have hx'' : 0 < |x| := zero_lt_one.trans hx'
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx'.le), pow_one]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos hx'').trans (sub_le_self _ zero_le_one)) (norm_nonneg _)
  have h := hNear.union hFar
  simpa only [union_compl_self, integrableOn_univ, f] using h

private lemma real_fourier_div_scale (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    𝓕 (fun x ↦ f (x/r)) ξ = r • 𝓕 f (r*ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  let g (x : ℝ) : ℂ := Real.fourierChar (-(x*(r*ξ))) • f x
  have he : (fun x : ℝ ↦ Real.fourierChar (-(x*ξ)) • f (x/r)) = fun x ↦ g (x/r) := by
    funext x
    unfold g
    have h : -((x/r)*(r*ξ)) = -(x*ξ) := by field_simp [hr.ne']
    rw [h]
  rw [he, Measure.integral_comp_div, abs_of_pos hr]

private lemma integral_fourier_schwartz_eq_value_zero (f : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ) = f 0 := by
  have hf : Integrable (𝓕 (f : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have h := f.integrable.fourierInv_fourier_eq hf (v := (0:ℝ)) f.continuous.continuousAt
  rw [Real.fourierInv_eq] at h
  simpa only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] using h

/-- Dilating the test by a factor of r changes the additive logarithmic
Fourier pairing by −log(r)f(0). -/
theorem realLogFourier_scale (f : 𝓢(ℝ, ℂ)) {r : ℝ} (hr : 0 < r) :
    realLogFourier (fun x ↦ f (x/r)) =
      realLogFourier f - (Real.log r : ℂ) * f 0 := by
  let g (x : ℝ) : ℂ := (Real.log |x/r| : ℂ) * 𝓕 (f : ℝ → ℂ) x
  unfold realLogFourier
  have he : (fun ξ : ℝ ↦ (Real.log |ξ| : ℂ) * 𝓕 (fun x ↦ f (x/r)) ξ) =
      fun ξ ↦ r • g (r*ξ) := by
    funext ξ
    rw [real_fourier_div_scale (f : ℝ → ℂ) hr]
    unfold g
    rw [mul_comm r ξ, mul_div_cancel_right₀ _ hr.ne', mul_comm ξ r]
    simp [Algebra.smul_def, mul_left_comm]
  rw [he, integral_smul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hr),
    smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hAE : g =ᵐ[volume] fun x : ℝ ↦
      (Real.log |x| : ℂ) * 𝓕 (f : ℝ → ℂ) x - (Real.log r : ℂ) * 𝓕 (f : ℝ → ℂ) x := by
    have hnz : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hnz] with x hx
    unfold g
    rw [abs_div, abs_of_pos hr, Real.log_div (abs_ne_zero.mpr hx) hr.ne', Complex.ofReal_sub, sub_mul]
  rw [integral_congr_ae hAE]
  have hF : Integrable (𝓕 (f : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have hLog : Integrable (fun x : ℝ ↦ (Real.log |x| : ℂ) * 𝓕 (f : ℝ → ℂ) x) := by
    simpa only [SchwartzMap.fourier_coe] using integrable_log_mul_schwartz (𝓕 f)
  rw [integral_sub hLog (hF.const_mul _), integral_const_mul,
    integral_fourier_schwartz_eq_value_zero]


/-- Real pole cutoff as printed in (B.4.3.13), with its closed endpoints. -/
noncomputable def printedLogCutoff (f : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in {x | δ ≤ |x|}, f x / |x|) + 2*f 0*Real.log δ

private lemma printedLogCutoff_eq (f : ℝ → ℝ) (δ : ℝ) :
    printedLogCutoff f δ = cutoffRealPole f δ := by
  have hae : {x : ℝ | δ ≤ |x|} =ᵐ[volume] {x : ℝ | δ < |x|} := by
    have h₁ : ∀ᵐ x : ℝ ∂volume, x ≠ δ := by simp [ae_iff]
    have h₂ : ∀ᵐ x : ℝ ∂volume, x ≠ -δ := by simp [ae_iff]
    filter_upwards [h₁, h₂] with x hx hx'
    change (δ ≤ |x|) = (δ < |x|)
    have hne : δ ≠ |x| := by
      intro he
      rcases le_or_gt 0 x with hpos | hneg
      · rw [abs_of_nonneg hpos] at he
        exact hx he.symm
      · rw [abs_of_neg hneg] at he
        exact hx' (by linarith)
    exact propext ⟨fun h ↦ lt_of_le_of_ne h hne, le_of_lt⟩
  change (∫ x in {x : ℝ | δ ≤ |x|}, f x / |x|) + 2*f 0*Real.log δ =
    (∫ x in {x : ℝ | δ < |x|}, f x / |x|) + 2*f 0*Real.log δ
  rw [setIntegral_congr_set hae]

private lemma exists_unit_plateau_schwartz :
    ∃ f : 𝓢(ℝ, ℝ), HasCompactSupport f ∧ f 0 = 1 ∧ Integrable (subtractedRealPole f) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let f : 𝓢(ℝ, ℝ) := bump.hasCompactSupport.toSchwartzMap bump.contDiff
  have hComp : HasCompactSupport f := bump.hasCompactSupport
  have hOne (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : f x = 1 := by
    apply bump.one_of_mem_closedBall
    have hv := abs_le.mpr hx
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hv
  have h0 : f 0 = 1 := hOne _ (by norm_num)
  refine ⟨f, hComp, h0, ?_⟩
  have hm : Measurable (subtractedRealPole f) := by
    unfold subtractedRealPole
    exact (f.continuous.measurable.sub (measurable_const.indicator measurableSet_Icc)).div measurable_abs
  refine f.integrable.mono hm.aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp [subtractedRealPole, indicator_of_mem hx, h0, hOne x hx]
  · have hx' : 1 < |x| := lt_of_not_ge (fun h ↦ hx (abs_le.mp h))
    rw [subtractedRealPole, indicator_of_notMem hx, sub_zero, norm_div, Real.norm_eq_abs |x|, abs_abs]
    exact div_le_self (norm_nonneg _) hx'.le

/-- The scale law forces the printed cutoff to be multiplied by one
half in any formula for the real additive logarithmic Fourier pairing. -/
theorem coefficient_forced_aux (c k : ℝ)
    (h : ∀ f : 𝓢(ℝ, ℝ), HasCompactSupport f → ∀ v : ℝ,
      Tendsto (printedLogCutoff f) (𝓝[>] (0 : ℝ)) (𝓝 v) →
      realLogFourier (fun x ↦ (f x : ℂ)) = ((-c*v-k*f 0 : ℝ) : ℂ)) :
    c = 1 / 2 := by
  obtain ⟨f, hComp, hF0, hF⟩ := exists_unit_plateau_schwartz
  let L := ∫ x, subtractedRealPole f x
  have hBase := (cutoffRealPole_tendsto hF).congr (fun δ ↦ (printedLogCutoff_eq _ δ).symm)
  have hEq := h f hComp L hBase
  let u : ℝˣ := Units.mk0 ((2:ℝ)⁻¹) (by norm_num)
  let e : ℝ ≃L[ℝ] ℝ := u • ContinuousLinearEquiv.refl ℝ ℝ
  let g : 𝓢(ℝ, ℝ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e f
  have heg (x : ℝ) : g x = f (x/2) := by
    change f (e x) = _
    have he : e x = x/2 := by
      dsimp [e,u]
      simp [div_eq_mul_inv, mul_comm]
    rw [he]
  have hCg : HasCompactSupport g := hComp.comp_homeomorph e.toHomeomorph
  have hg0 : g 0 = 1 := by rw [heg, zero_div, hF0]
  have hScale := cutoffRealPole_scaled_tendsto hF (by norm_num : (0:ℝ) < 2)
  have hPrint := hScale.congr (fun δ ↦ (printedLogCutoff_eq _ δ).symm)
  have hPg : Tendsto (printedLogCutoff g) (𝓝[>] (0:ℝ)) (𝓝 (L+2*f 0*Real.log 2)) := by
    have hFunctions : (g : ℝ → ℝ) = fun x ↦ f (x/2) := funext heg
    rw [hFunctions]
    exact hPrint
  have hEg := h g hCg (L+2*f 0*Real.log 2) hPg
  let fC : 𝓢(ℝ, ℂ) := f.postcompCLM Complex.ofRealCLM
  have hfc (x : ℝ) : fC x = (f x : ℂ) := rfl
  have hFourier := realLogFourier_scale fC (by norm_num : (0:ℝ) < 2)
  rw [show (fC : ℝ → ℂ) = fun x ↦ (f x : ℂ) from funext hfc] at hFourier
  simp_rw [← heg] at hFourier
  rw [hEg, hEq, hF0, hg0] at hFourier
  have hRe := congrArg Complex.re hFourier
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero, mul_one] at hRe
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (2*c-1)*Real.log 2 = 0 := by nlinarith only [hRe]
  have hc := (mul_eq_zero.mp he).resolve_right hlog.ne'
  linarith only [hc]

/-- The unhalved version printed in (B.4.3.13) fails for some compact
smooth test, for any fixed choice of the pole constant. -/
theorem real_log_fourier_cutoff_scaling_mismatch (k : ℝ) :
    ¬ ∀ f : 𝓢(ℝ, ℝ), HasCompactSupport f → ∀ v : ℝ,
      Tendsto (printedLogCutoff f) (𝓝[>] (0 : ℝ)) (𝓝 v) →
      realLogFourier (fun x ↦ (f x : ℂ)) = ((-v-k*f 0 : ℝ) : ℂ) := by
  intro h
  have hh : (1 : ℝ) = 1 / 2 := coefficient_forced_aux 1 k (by simpa using h)
  norm_num at hh

end MasulloAudit

open MasulloAudit MeasureTheory Filter FourierTransform Set
open scoped Topology SchwartzMap FourierTransform

theorem solution (c k : ℝ)
    (h : ∀ f : 𝓢(ℝ, ℝ), HasCompactSupport f → ∀ v : ℝ,
      Tendsto (fun δ : ℝ ↦ (∫ x in {x : ℝ | δ ≤ |x|}, f x / |x|) +
        2*f 0*Real.log δ) (𝓝[>] (0 : ℝ)) (𝓝 v) →
      (∫ ξ : ℝ, (Real.log |ξ| : ℂ) * 𝓕 (fun x : ℝ ↦ (f x : ℂ)) ξ) =
        ((-c*v-k*f 0 : ℝ) : ℂ)) :
    c = 1 / 2 := by
  exact coefficient_forced_aux c k h
