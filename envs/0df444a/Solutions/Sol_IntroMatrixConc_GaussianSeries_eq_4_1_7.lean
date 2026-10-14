-- Prove2me | solution 1 for IntroMatrixConc.GaussianSeries.eq_4_1_7
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T04:02:09.149115+00:00
-- url     : https://prove2.me/submissions/20558952-0813-4812-920e-302c1453f861

import Theorems.Thm_TroppMatrixConcentration_ch4_matrix_series
import Theorems.Thm_IntroMatrixConc_GaussianSeries_jensen_lower
import Theorems.Thm_IntroMatrixConc_GaussianSeries_tail_integration
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator ENNReal
namespace TroppSquaredNormRoot
lemma exponential_integral (K c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => K * Real.exp (-t / c)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, K * Real.exp (-t / c)) = K * c := by
  have he : (fun t : ℝ => K * Real.exp (-t / c)) =
      (fun t => K * Real.exp ((-c⁻¹) * t)) := by
    funext t
    congr 1
    congr 1
    ring
  rw [he]
  have hn : -c⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hc)
  refine ⟨(integrableOn_exp_mul_Ioi hn 0).const_mul K, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi hn 0]
  simp [ne_of_gt hc]

lemma nonnegative_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hm : Measurable f) (hn : ∀ ω, 0 ≤ f ω)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 < t → (μ {ω | t ≤ f ω}).toReal ≤ K * Real.exp (-t / c)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ K * c := by
  have hnn : 0 ≤ᵐ[μ] f := Eventually.of_forall hn
  obtain ⟨hmajor, hvalue⟩ := exponential_integral K c hc
  have hmajnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => K * Real.exp (-t / c)) :=
    Eventually.of_forall (fun t => mul_nonneg hK (Real.exp_pos _).le)
  have hbound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (K * Real.exp (-t / c)) := by
    rw [lintegral_eq_lintegral_meas_le μ hnn hm.aemeasurable]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (mul_nonneg hK (Real.exp_pos _).le)).mpr
      (htail t ht)
  have hfin : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hmajor.lintegral_lt_top.ne hbound
  have hi : Integrable f μ := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hnn).mp hfin
  refine ⟨hi, ?_⟩
  have he := ENNReal.toReal_mono hmajor.lintegral_lt_top.ne hbound
  rw [← integral_eq_lintegral_of_nonneg_ae hnn hi.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae hmajnn hmajor.aestronglyMeasurable, hvalue] at he
  exact he


lemma square_zero_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ) (hm : Measurable u)
    (hu : ∀ ω, 0 ≤ u ω) (D : ℕ)
    (htail : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ u ω}).toReal ≤ gaussianSeriesTail D 0 t) :
    Integrable (fun ω => u ω ^ 2) μ ∧ (∫ ω, u ω ^ 2 ∂μ) ≤ 0 := by
  suffices h : Integrable (fun ω => u ω ^ 2) μ ∧ (∫ ω, u ω ^ 2 ∂μ) ≤ 0 * 1 by
    simpa only [zero_mul] using h
  apply nonnegative_exp_tail μ (fun ω => u ω ^ 2) (hm.pow_const 2)
    (fun ω => sq_nonneg _) 0 1 (by norm_num) (by norm_num)
  intro t ht
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h := htail (Real.sqrt t) (Real.sqrt_nonneg t)
  simp [gaussianSeriesTail, ne_of_gt hspos] at h
  have he : {ω | t ≤ u ω ^ 2} = {ω | Real.sqrt t ≤ u ω} := by
    ext ω
    change t ≤ u ω ^ 2 ↔ Real.sqrt t ≤ u ω
    rw [Real.sqrt_le_iff]
    exact ⟨fun h => ⟨hu ω, h⟩, fun h => h.2⟩
  simpa only [he, zero_mul] using h

end TroppSquaredNormRoot

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂]
    (B : Fin N → Matrix (Fin d₁) (Fin d₂) ℂ)
    (g : Fin N → Ω → ℝ)
    (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : ∀ k, standardGaussianLaw μ (g k)) :
    let Z := fun ω => ∑ k, g k ω • B k
    let v := rectSecondMoment μ Z
    Integrable (fun ω => spectralNorm (Z ω) ^ 2) μ ∧
      v ≤ ∫ ω, spectralNorm (Z ω) ^ 2 ∂μ ∧
      (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ≤
        2 * v * (1 + Real.log (d₁ + d₂)) := by
  let Z := fun ω => ∑ k, g k ω • B k
  let v := rectSecondMoment μ Z
  change Integrable (fun ω => spectralNorm (Z ω) ^ 2) μ ∧
    v ≤ (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ∧
    (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ≤ 2 * v * (1 + Real.log (d₁ + d₂))
  have hZ : Measurable Z := by unfold Z; fun_prop
  have H := TroppMatrixConcentration.ch4_matrix_series μ B g hMeas hIndep (Or.inl hLaw)
  obtain ⟨hvar, hmean, htail⟩ := H
  change ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
    gaussianSeriesTail (d₁ + d₂) v t at htail
  have hlower := IntroMatrixConc.GaussianSeries.jensen_lower μ B g hMeas hIndep hLaw
  change v ≤ (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) at hlower
  by_cases hv0 : v = 0
  · have hzero := TroppSquaredNormRoot.square_zero_tail μ (fun ω => ‖Z ω‖)
      hZ.norm (fun ω => norm_nonneg _) (d₁ + d₂)
      (by simpa only [hv0, TroppMatrixConcentration.spectralNorm] using htail)
    refine ⟨hzero.1, hlower, ?_⟩
    simpa only [hv0, mul_zero, zero_mul, TroppMatrixConcentration.spectralNorm] using hzero.2
  · have hvnn : 0 ≤ v := by
      unfold v rectSecondMoment TroppMatrixConcentration.spectralNorm
      exact le_max_of_le_left (norm_nonneg _)
    have hv : 0 < v := lt_of_le_of_ne hvnn (Ne.symm hv0)
    have hD : (1 : ℝ) < (d₁ + d₂ : ℕ) := by
      have h₁ := NeZero.pos d₁
      have h₂ := NeZero.pos d₂
      exact_mod_cast (show 1 < d₁ + d₂ by omega)
    have hlog : 0 < Real.log (d₁ + d₂ : ℕ) := Real.log_pos hD
    let a := Real.sqrt (2 * v * Real.log (d₁ + d₂ : ℕ))
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = 2 * v * Real.log (d₁ + d₂ : ℕ) := Real.sq_sqrt (by positivity)
    have ht : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp (-(t ^ 2) / (2*v)) := by
      intro t ht
      simpa only [gaussianSeriesTail, if_neg hv0] using htail t ht
    obtain ⟨hi, hb⟩ := IntroMatrixConc.GaussianSeries.tail_integration μ Z hZ hv ht a ha
    refine ⟨hi, hlower, ?_⟩
    have he : Real.exp (-(a ^ 2) / (2*v)) = (d₁ + d₂ : ℝ)⁻¹ := by
      rw [ha2]
      have hearg : -(2 * v * Real.log (d₁ + d₂ : ℕ)) / (2*v) = -Real.log (d₁ + d₂ : ℕ) := by
        field_simp
      rw [hearg, Real.exp_neg, Real.exp_log (by linarith : (0 : ℝ) < (d₁ + d₂ : ℕ))]
      simp only [Nat.cast_add]
    change (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ≤
      a ^ 2 + 2 * v * (d₁ + d₂ : ℕ) * Real.exp (-(a ^ 2) / (2*v)) at hb
    rw [he, ha2] at hb
    have hdim : (d₁ + d₂ : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (d₁ + d₂ : ℕ) := lt_trans zero_lt_one hD
      simpa only [Nat.cast_add] using ne_of_gt hpos
    have hrem : 2 * v * (d₁ + d₂ : ℕ) * (d₁ + d₂ : ℝ)⁻¹ = 2*v := by
      simp only [Nat.cast_add]
      field_simp
    rw [hrem] at hb
    simp only [Nat.cast_add] at hb
    nlinarith

#print axioms solution
