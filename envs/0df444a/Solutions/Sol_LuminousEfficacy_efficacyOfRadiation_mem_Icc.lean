-- Prove2me | solution 1 for LuminousEfficacy.efficacyOfRadiation_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:10:42.067495+00:00
-- url     : https://prove2.me/submissions/3643071f-6169-4a39-8195-8b47e4e979ee

import Definitions.Def_luminous_efficacy

open MeasureTheory
open LuminousEfficacy

theorem W4a_LuminousEfficacy_luminousFlux_nonneg (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ)
    (hKmax : 0 ≤ Kmax) (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) :
    0 ≤ luminousFlux Kmax V mu := by
  unfold luminousFlux
  exact mul_nonneg hKmax (integral_nonneg hV.nonneg)

theorem W4a_LuminousEfficacy_int_le (V : ℝ → ℝ) (peak : ℝ)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    ∫ l, V l ∂mu ≤ radiantFlux mu := by
  have h := integral_mono_of_nonneg (μ := mu) (f := V) (g := fun _ => (1 : ℝ))
    (ae_of_all _ hV.nonneg) (integrable_const 1) (ae_of_all _ hV.le_one)
  simpa [radiantFlux, measureReal_def] using h

theorem W4a_LuminousEfficacy_luminousFlux_le_max_mul_radiantFlux (Kmax : ℝ) (V : ℝ → ℝ)
    (peak : ℝ) (hKmax : 0 ≤ Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    luminousFlux Kmax V mu ≤ Kmax * radiantFlux mu := by
  unfold luminousFlux
  exact mul_le_mul_of_nonneg_left (W4a_LuminousEfficacy_int_le V peak hV mu) hKmax

theorem solution (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ)
    (hKmax : 0 ≤ Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) :
    efficacyOfRadiation Kmax V mu ∈ Set.Icc 0 Kmax := by
  unfold efficacyOfRadiation
  refine ⟨div_nonneg (W4a_LuminousEfficacy_luminousFlux_nonneg Kmax V peak hKmax hV mu)
    hmu.le, ?_⟩
  rw [div_le_iff₀ hmu]
  exact W4a_LuminousEfficacy_luminousFlux_le_max_mul_radiantFlux Kmax V peak hKmax hV mu

theorem W4a_LuminousEfficacy_luminousEfficiency_mem_Icc (Kmax : ℝ) (V : ℝ → ℝ) (peak : ℝ)
    (hKmax : 0 < Kmax)
    (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) :
    luminousEfficiency Kmax V mu ∈ Set.Icc 0 1 := by
  obtain ⟨h0, h1⟩ :=
    solution Kmax V peak hKmax.le hV mu hmu
  unfold luminousEfficiency
  refine ⟨div_nonneg h0 hKmax.le, ?_⟩
  rw [div_le_iff₀ hKmax]
  linarith

theorem W4a_LuminousEfficacy_efficacyOfSource_le_efficacyOfRadiation (Kmax : ℝ) (V : ℝ → ℝ)
    (peak : ℝ)
    (hKmax : 0 ≤ Kmax) (hV : IsLuminosityFunction V peak) (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) (P : ℝ) (hP : radiantFlux mu ≤ P) :
    efficacyOfSource Kmax V mu P ≤ efficacyOfRadiation Kmax V mu ∧
      efficacyOfSource Kmax V mu P ≤ Kmax := by
  have h1 : efficacyOfSource Kmax V mu P ≤ efficacyOfRadiation Kmax V mu := by
    unfold efficacyOfSource efficacyOfRadiation
    exact div_le_div_of_nonneg_left
      (W4a_LuminousEfficacy_luminousFlux_nonneg Kmax V peak hKmax hV mu) hmu hP
  exact ⟨h1, h1.trans
    (solution Kmax V peak hKmax hV mu hmu).2⟩

theorem W4a_LuminousEfficacy_efficacy_eq_zero_of_invisible (Kmax : ℝ) (V : ℝ → ℝ)
    (mu : Measure ℝ)
    (hV : ∀ᵐ l ∂mu, V l = 0) :
    luminousFlux Kmax V mu = 0 ∧ efficacyOfRadiation Kmax V mu = 0 := by
  have h : luminousFlux Kmax V mu = 0 := by
    unfold luminousFlux
    rw [integral_eq_zero_of_ae hV, mul_zero]
  refine ⟨h, ?_⟩
  unfold efficacyOfRadiation
  rw [h, zero_div]

theorem W4a_LuminousEfficacy_efficacyOfRadiation_dirac_peak (Kmax : ℝ) (V : ℝ → ℝ)
    (peak : ℝ)
    (hV : IsLuminosityFunction V peak) :
    radiantFlux (Measure.dirac peak) = 1 ∧
      efficacyOfRadiation Kmax V (Measure.dirac peak) = Kmax := by
  have h1 : radiantFlux (Measure.dirac peak) = 1 := by simp [radiantFlux]
  refine ⟨h1, ?_⟩
  unfold efficacyOfRadiation luminousFlux
  rw [h1, integral_dirac, hV.peak_eq_one]
  simp

theorem W4a_LuminousEfficacy_efficacyOfRadiation_smul (Kmax : ℝ) (V : ℝ → ℝ)
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmu : 0 < radiantFlux mu) (c : ENNReal) (hc : c ≠ 0) (hctop : c ≠ ⊤) :
    efficacyOfRadiation Kmax V (c • mu) = efficacyOfRadiation Kmax V mu := by
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc hctop
  have hR : radiantFlux (c • mu) = c.toReal * radiantFlux mu := by
    simp [radiantFlux, ENNReal.toReal_mul]
  unfold efficacyOfRadiation luminousFlux
  rw [hR, integral_smul_measure, smul_eq_mul]
  field_simp

theorem W4a_LuminousEfficacy_efficacyOfRadiation_ofDensity (Kmax : ℝ) (V Phi : ℝ → ℝ)
    (peak : ℝ)
    (hV : IsLuminosityFunction V peak) (hPhimeas : Measurable Phi)
    (hPhinonneg : ∀ l, 0 ≤ Phi l)
    (hPhiint : Integrable Phi) (hPhipos : 0 < ∫ l, Phi l) :
    radiantFlux (ofDensity Phi) = ∫ l, Phi l ∧
      efficacyOfRadiation Kmax V (ofDensity Phi)
        = (Kmax * ∫ l, V l * Phi l) / ∫ l, Phi l := by
  have hR : radiantFlux (ofDensity Phi) = ∫ l, Phi l := by
    unfold radiantFlux ofDensity
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hPhiint (ae_of_all _ hPhinonneg),
      ENNReal.toReal_ofReal (integral_nonneg hPhinonneg)]
  refine ⟨hR, ?_⟩
  unfold efficacyOfRadiation luminousFlux
  rw [hR]
  congr 2
  have h := integral_withDensity_eq_integral_smul (μ := (volume : Measure ℝ))
    (f := fun l => (Phi l).toNNReal) hPhimeas.real_toNNReal V
  have hd : ofDensity Phi = (volume : Measure ℝ).withDensity
      (fun l => (((Phi l).toNNReal : NNReal) : ENNReal)) := rfl
  rw [hd, h]
  congr 1
  funext l
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hPhinonneg l), mul_comm]

theorem W4a_LuminousEfficacy_max_photopic (V : ℝ → ℝ) (hV : IsLuminosityFunction V 555) :
    IsGreatest {K : ℝ | ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ 0 < radiantFlux mu ∧
      K = efficacyOfRadiation Km V mu} 683.002 := by
  obtain ⟨h1, h2⟩ := W4a_LuminousEfficacy_efficacyOfRadiation_dirac_peak Km V 555 hV
  refine ⟨⟨Measure.dirac 555, inferInstance, by rw [h1]; norm_num, ?_⟩, ?_⟩
  · rw [h2]; rfl
  · rintro K ⟨mu, hfin, hpos, rfl⟩
    have hK : (0 : ℝ) ≤ Km := by unfold Km; norm_num
    have := (solution Km V 555 hK hV mu hpos).2
    exact this

theorem W4a_LuminousEfficacy_max_scotopic (V : ℝ → ℝ) (hV : IsLuminosityFunction V 507) :
    IsGreatest {K : ℝ | ∃ mu : Measure ℝ, IsFiniteMeasure mu ∧ 0 < radiantFlux mu ∧
      K = efficacyOfRadiation KmScotopic V mu} 1700 := by
  obtain ⟨h1, h2⟩ := W4a_LuminousEfficacy_efficacyOfRadiation_dirac_peak KmScotopic V 507 hV
  refine ⟨⟨Measure.dirac 507, inferInstance, by rw [h1]; norm_num, ?_⟩, ?_⟩
  · rw [h2]; rfl
  · rintro K ⟨mu, hfin, hpos, rfl⟩
    have hK : (0 : ℝ) ≤ KmScotopic := by unfold KmScotopic; norm_num
    have := (solution KmScotopic V 507 hK hV mu hpos).2
    exact this
