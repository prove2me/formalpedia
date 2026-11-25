-- Prove2me | solution 1 for Newton.mollifier_convolution_diff_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:41.381804+00:00
-- url     : https://prove2.me/submissions/4251c1fd-40db-4f4e-be0c-fd9d2fd2bcaa

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Theorems.Thm_Newton_scaled_mollifier_L1_norm_one
import Theorems.Thm_Newton_convolution_diff_bound_L1

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (g f₀ : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hg : Integrable g volume)
    (hf₀ : Integrable f₀ volume)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x)
    (hψ_int : ∫ x, ψ x = 1) :
    ∀ η : ℝ, 0 < η → η < 1 →
      eLpNorm (fun x =>
        (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
        (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
        1 volume ≤
      eLpNorm (fun x => g x - f₀ x) 1 volume := by
  intro η hη_pos _hη_lt_one
  -- Define the scaled mollifier (real and complex versions).
  set ψηR : (Fin n → ℝ) → ℝ :=
    fun y => η^(-(n : ℝ)) * ψ (fun i => y i / η) with hψηR_def
  set ψηC : (Fin n → ℝ) → ℂ := fun y => (ψηR y : ℝ) with hψηC_def
  -- L¹ norm of the scaled mollifier equals 1.
  -- First, obtain integrability of ψ from the normalization assumption.
  have hψ_integrable : Integrable ψ volume := by
    by_contra hnot
    have h0 : ∫ x, ψ x ∂volume = 0 := by
      simp [MeasureTheory.integral_undef hnot]  -- integral is 0 if not integrable
    have : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ∫ x, ψ x ∂volume := by simpa using hψ_int.symm
        _ = 0 := h0
    exact one_ne_zero this
  have hψηR_L1 : eLpNorm ψηR 1 volume = ENNReal.ofReal 1 := by
    simpa [hψηR_def]
      using scaled_mollifier_L1_norm_one (ψ := ψ) (η := η)
        hη_pos hψ_integrable hψ_int hψ_nonneg
  -- Transfer the L¹ norm equality to the complex-valued version.
  have hψηC_L1 : eLpNorm ψηC 1 volume = ENNReal.ofReal 1 := by
    have h_eq : eLpNorm ψηC 1 volume = eLpNorm ψηR 1 volume := by
      refine eLpNorm_congr_norm_ae (μ := volume) (p := (1 : ℝ≥0∞)) ?_
      exact Filter.Eventually.of_forall (fun x => by simp [ψηC, Real.norm_eq_abs])
    simpa [h_eq] using hψηR_L1
  -- Obtain integrability of the complex scaled mollifier from its finite L¹ norm.
  have hψηC_meas : AEStronglyMeasurable ψηC volume := by
    -- Build AEMeasurable for the real scaled mollifier, then lift to complex via ofReal.
    have hψ_meas : AEMeasurable ψ volume :=
      hψ_integrable.aestronglyMeasurable.aemeasurable
    have h_scale_meas : Measurable fun y : (Fin n → ℝ) => (1 / η : ℝ) • y :=
      (continuous_const_smul (1 / η : ℝ)).measurable
    -- Compute the pushforward of volume under scaling and derive quasi-measure-preserving.
    have h_map_scale :
        Measure.map (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y) volume
          = ENNReal.ofReal (abs ((LinearMap.det
                ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
      have h_eq_fn : (⇑((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : (Fin n → ℝ) → (Fin n → ℝ)) = fun y : (Fin n → ℝ) => (1 / η : ℝ) • y := by
        funext y; simp
      rw [← h_eq_fn]
      exact Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (f := ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))))
          (by
            have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη_pos)
            have hdet :
                LinearMap.det
                    ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                  = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
              simp
            have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
              pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
            simpa [hdet] using hpow2)
    have h_scale_qmp :
        Measure.QuasiMeasurePreserving (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y)
          volume volume := by
      refine ⟨h_scale_meas, ?_⟩
      have h_le :
          Measure.map (fun y : (Fin n → ℝ) => (1 / η : ℝ) • y) volume ≤
            ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
        simpa [h_map_scale] using (le_of_eq h_map_scale)
      exact Measure.absolutelyContinuous_of_le_smul h_le
    -- Compose along the quasi-measure-preserving scaling map.
    have h_comp : AEMeasurable (fun y => ψ ((1 / η) • y)) volume :=
      hψ_meas.comp_quasiMeasurePreserving h_scale_qmp
    have h_c_meas : AEMeasurable (fun _ : (Fin n → ℝ) => η^(-(n : ℝ))) volume :=
      (measurable_const : Measurable fun _ : (Fin n → ℝ) => η^(-(n : ℝ))).aemeasurable
    -- Rewrite the argument `η⁻¹ • x` to the coordinate form `fun i => x i / η`.
    have h_arg_eq_inv :
        (fun x : (Fin n → ℝ) => ψ (η⁻¹ • x))
          = (fun x : (Fin n → ℝ) => ψ (fun i => x i / η)) := by
      funext x
      have : (η⁻¹ : ℝ) • x = (fun i => x i * η⁻¹) := by
        funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      simp [div_eq_mul_inv, this]
    have h_comp' : AEMeasurable (fun y : (Fin n → ℝ) => ψ ((1 / η) • y)) volume := by
      simpa [one_div] using h_comp
    have h_comp2 : AEMeasurable (fun y : (Fin n → ℝ) => ψ (fun i => y i / η)) volume := by
      -- Convert `((1/η) • y)` to `(η⁻¹ • y)` and then rewrite by coordinates.
      have h_comp'' : AEMeasurable (fun y : (Fin n → ℝ) => ψ (η⁻¹ • y)) volume := by
        simpa [one_div] using h_comp'
      simpa [h_arg_eq_inv] using h_comp''
    have hψηR_ae : AEMeasurable ψηR volume :=
      h_c_meas.mul h_comp2
    have hψηR_sm : AEStronglyMeasurable ψηR volume := hψηR_ae.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp_aemeasurable hψηR_sm.aemeasurable).aestronglyMeasurable
  have hψηC_int : Integrable ψηC volume := by
    -- From measurability and the finite L¹ norm we get membership in L¹, hence integrable.
    have h_lt_top : eLpNorm ψηC 1 volume < (⊤ : ℝ≥0∞) := by
      simp [hψηC_L1]
    have h_mem : MemLp ψηC 1 volume := ⟨hψηC_meas, h_lt_top⟩
    simpa using (memLp_one_iff_integrable (μ := volume)).1 h_mem
  -- Apply the L¹ convolution difference bound with the scaled mollifier.
  have h_bound :=
    convolution_diff_bound_L1 (f₁ := g) (f₂ := f₀)
      (ψ := ψηC) hg hf₀ hψηC_int
  -- Replace the multiplier by 1 using the computed L¹ norm.
  have hψηC_L1_one : eLpNorm ψηC 1 volume = (1 : ℝ≥0∞) := by
    simpa using hψηC_L1.trans (by simp)
  have h_form_total :
      (fun x =>
        (∫ y, g (x - y) * (↑(ψηR y) : ℂ)) - ∫ y, f₀ (x - y) * (↑(ψηR y) : ℂ))
        = (fun x =>
            (∫ y, g (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ (fun i => y i / η)))) -
              ∫ y, f₀ (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ (fun i => y i / η)))) := by
    funext x
    simp [ψηR, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
          Real.rpow_neg (le_of_lt hη_pos), Real.rpow_natCast, mul_comm, mul_assoc]
  -- Apply the bound after rewriting both convolution terms inside the difference.
  simpa [ψηC, hψηC_def, hψηC_L1_one, one_mul, h_form_total]
    using h_bound
end Newton
