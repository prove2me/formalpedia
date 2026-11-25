-- Prove2me | solution 1 for IActThereforeIAm.entropy_le_zero_on_unit_cube
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T18:32:00.591354+00:00
-- url     : https://prove2.me/submissions/0365c38c-ad97-4a95-8ab2-9d511be32c7d

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

lemma en_le (x : ℝ) (hx : 0 ≤ x) : Real.negMulLog x ≤ 1 - x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · have h := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
    rw [Real.log_inv] at h
    have : x * (-Real.log x) ≤ x * (x⁻¹ - 1) := mul_le_mul_of_nonneg_left h hx.le
    rw [mul_sub, mul_inv_cancel₀ hx.ne'] at this
    unfold Real.negMulLog; linarith

lemma en_eq (x : ℝ) (hx : 0 ≤ x) (h : Real.negMulLog x = 1 - x) : x = 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp at h
  · by_contra hne
    have h1 := Real.log_lt_sub_one_of_pos (inv_pos.2 hx) (by simpa using hne)
    rw [Real.log_inv] at h1
    have : x * (-Real.log x) < x * (x⁻¹ - 1) := mul_lt_mul_of_pos_left h1 hx
    rw [mul_sub, mul_inv_cancel₀ hx.ne'] at this
    unfold Real.negMulLog at h; linarith

lemma en_meas (d : ℕ) : MeasurableSet (unitCube d) := by
  unfold unitCube; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma en_vol (d : ℕ) : volume (unitCube d) = 1 := by
  unfold unitCube; rw [Real.volume_pi_Ioo]; simp

lemma en_cube (d : ℕ) :
    ((volume : Measure (Fin d → ℝ)).restrict (unitCube d)) ≪ volume ∧
    (fun z => Real.negMulLog
      (((volume : Measure (Fin d → ℝ)).restrict (unitCube d)).rnDeriv volume z).toReal)
      =ᵐ[volume] 0 := by
  refine ⟨Measure.absolutelyContinuous_of_le Measure.restrict_le_self, ?_⟩
  filter_upwards [Measure.rnDeriv_restrict_self (volume : Measure (Fin d → ℝ)) (en_meas d)]
    with z hz
  rw [hz]
  by_cases hzC : z ∈ unitCube d <;> simp [Set.indicator, hzC]

end IActThereforeIAm

open IActThereforeIAm in
theorem solution {d : ℕ} (μ : MeasureTheory.Measure (Fin d → ℝ)) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : μ (unitCube d)ᶜ = 0) :
    diffEntropy μ ≤ 0 ∧ (diffEntropy μ = 0 ↔ μ = MeasureTheory.volume.restrict (unitCube d)) := by
  classical
  have hC : MeasurableSet (unitCube d) := en_meas d
  have hvC : volume (unitCube d) = 1 := en_vol d
  obtain ⟨hνac, hνz⟩ := en_cube d
  have hνint : Integrable (fun z => Real.negMulLog
      (((volume : Measure (Fin d → ℝ)).restrict (unitCube d)).rnDeriv volume z).toReal) volume :=
    (integrable_zero _ _ _).congr hνz.symm
  have hν0 : diffEntropy ((volume : Measure (Fin d → ℝ)).restrict (unitCube d)) = 0 := by
    unfold diffEntropy; rw [if_pos ⟨hνac, hνint⟩, integral_congr_ae hνz]; simp
  by_cases hcond : μ ≪ volume ∧
      Integrable (fun z => Real.negMulLog (μ.rnDeriv volume z).toReal) volume
  swap
  · have hb : diffEntropy μ = ⊥ := by unfold diffEntropy; rw [if_neg hcond]
    refine ⟨by rw [hb]; exact bot_le, ?_⟩
    rw [hb]; constructor
    · intro h; exact absurd h EReal.bot_ne_zero
    · intro h; subst h; exact absurd ⟨hνac, hνint⟩ hcond
  obtain ⟨hac, hint⟩ := hcond
  have hE : diffEntropy μ = ((∫ z, Real.negMulLog (μ.rnDeriv volume z).toReal : ℝ) : EReal) := by
    unfold diffEntropy; rw [if_pos ⟨hac, hint⟩]
  have hoff : ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)), z ∈ (unitCube d)ᶜ → μ.rnDeriv volume z = 0 := by
    have h1 : ∫⁻ z in (unitCube d)ᶜ, μ.rnDeriv volume z ∂volume = 0 := by
      rw [Measure.setLIntegral_rnDeriv hac]; exact hμ
    rw [lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _)] at h1
    exact (ae_restrict_iff' hC.compl).1 h1
  have hfin := Measure.rnDeriv_lt_top μ (volume : Measure (Fin d → ℝ))
  set f : (Fin d → ℝ) → ℝ := fun z => (μ.rnDeriv volume z).toReal with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => ENNReal.toReal_nonneg
  have hfi : Integrable f volume := Measure.integrable_toReal_rnDeriv
  set h : (Fin d → ℝ) → ℝ := fun z =>
    (unitCube d).indicator (fun z => 1 - f z) z - Real.negMulLog (f z) with hh
  have hh0 : 0 ≤ᵐ[volume] h := by
    filter_upwards [hoff] with z hz
    by_cases hzC : z ∈ unitCube d
    · simp only [hh, Pi.zero_apply, Set.indicator_of_mem hzC]
      linarith [en_le _ (hf0 z)]
    · have : f z = 0 := by simp [hf, hz hzC]
      simp [hh, Set.indicator, hzC, this]
  have hc1 : IntegrableOn (fun _ => (1:ℝ)) (unitCube d) volume :=
    integrableOn_const (by rw [hvC]; exact ENNReal.one_ne_top)
  have hion : IntegrableOn (fun z => 1 - f z) (unitCube d) volume := hc1.sub hfi.integrableOn
  have hhi : Integrable h volume := (hion.integrable_indicator hC).sub hint
  have hμC : μ (unitCube d) = 1 := (prob_compl_eq_zero_iff hC).1 hμ
  have hint_h : ∫ z, h z = - ∫ z, Real.negMulLog (f z) := by
    simp only [hh]
    rw [integral_sub (hion.integrable_indicator hC) hint, integral_indicator hC,
      integral_sub hc1 hfi.integrableOn,
      setIntegral_const, Measure.setIntegral_toReal_rnDeriv hac]
    simp [Measure.real, hvC, hμC]
    rfl
  have hEle : ∫ z, Real.negMulLog (f z) ≤ 0 := by
    have := integral_nonneg_of_ae hh0; linarith
  refine ⟨by rw [hE]; exact_mod_cast hEle, ?_⟩
  constructor
  · intro h0
    rw [hE] at h0
    have h0' : ∫ z, Real.negMulLog (f z) = 0 := by exact_mod_cast h0
    have hz : h =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg_ae hh0 hhi).1 (by linarith)
    have hrn : μ.rnDeriv volume =ᵐ[volume] (unitCube d).indicator 1 := by
      filter_upwards [hz, hoff, hfin] with z h1 h2 h3
      by_cases hzC : z ∈ unitCube d
      · simp only [hh, Pi.zero_apply, Set.indicator_of_mem hzC] at h1
        have hf1 : f z = 1 := en_eq _ (hf0 z) (by linarith)
        rw [Set.indicator_of_mem hzC]
        simp only [hf] at hf1
        simpa using (ENNReal.toReal_eq_one_iff _).1 hf1
      · rw [h2 hzC]; simp [Set.indicator, hzC]
    rw [← Measure.withDensity_rnDeriv_eq μ volume hac, withDensity_congr_ae hrn,
      withDensity_indicator_one hC]
  · intro h1
    rw [h1]; exact hν0
