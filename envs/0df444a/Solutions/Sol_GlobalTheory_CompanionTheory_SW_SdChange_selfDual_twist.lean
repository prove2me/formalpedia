-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:14.346396+00:00
-- url     : https://prove2.me/submissions/4c33fc43-fa73-4103-a381-587a8e3b9770

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTwistBySymmetricAuto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SdChange
namespace GlobalTheory.CompanionTheory.SW.SdChange
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V),
    (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ →
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ hsd B hsym c hc
  obtain ⟨hHaar, hinv⟩ := hsd
  have hemb : MeasurableEmbedding B := (B.toHomeomorph).measurableEmbedding
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : μ.map B = 0 := by simpa using hc
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne μ) h0
  have hs0 : NNReal.sqrt c ≠ 0 := by simpa using hc0
  have hss : NNReal.sqrt c * NNReal.sqrt c = c := NNReal.mul_self_sqrt c
  generalize NNReal.sqrt c = s at hs0 hss ⊢
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ (inv_ne_zero hs0), ?_⟩
  intro Φ _ _ hint z
  let H : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ x (B y) ∂(s⁻¹ • μ) = s⁻¹ • H (B y) :=
    fun y => integral_smul_nnreal_measure _ _
  simp only [h1] at hint ⊢
  have hsE : ((s⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hs0
  have hint2 : Integrable (fun y => H (B y)) μ := by
    have h2 : Integrable (fun y => s⁻¹ • H (B y)) μ := by
      have h3 : s⁻¹ • μ = ((s⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := rfl
      rw [h3] at hint
      exact (integrable_smul_measure hsE ENNReal.coe_ne_top).1 hint
    have h4 := h2.smul (s : ℝ)
    refine h4.congr (Filter.Eventually.of_forall fun y => ?_)
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
    simp [NNReal.smul_def, smul_smul]
    rw [← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
  have hintH : Integrable H μ := by
    have h5 : Integrable H (μ.map B) := (hemb.integrable_map_iff).2 hint2
    rw [hc] at h5
    have h6 : c • μ = (c : ℝ≥0∞) • μ := rfl
    rw [h6] at h5
    exact (integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top).1 h5
  have hI := hinv Φ ‹_› ‹_› hintH z
  have h7 : ∫ w, H w * χ w z ∂(μ.map B) = c • ∫ w, H w * χ w z ∂μ := by
    rw [hc]; exact integral_smul_nnreal_measure _ _
  have h8 : ∫ w, H w * χ w z ∂(μ.map B) = ∫ y, H (B y) * χ (B y) z ∂μ :=
    hemb.integral_map _
  rw [integral_smul_nnreal_measure]
  have h9 : ∀ y, (s⁻¹ • H (B y)) * χ y (B z) = s⁻¹ • (H (B y) * χ (B y) z) := by
    intro y; rw [hsym, smul_mul_assoc]
  simp only [h9]
  have h10 : ∫ y, H (B y) * χ (B y) z ∂μ = c • Φ (-z) := by
    rw [← h8, h7]
    exact congrArg (c • ·) hI
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hcR : (c : ℝ) = (s : ℝ) * s := by exact_mod_cast hss.symm
  simp only [NNReal.smul_def] at h10 ⊢
  rw [integral_smul, h10, smul_smul, smul_smul, hcR]
  have h11 : (((s⁻¹ : ℝ≥0) : ℝ)) = (s : ℝ)⁻¹ := by simp
  rw [h11]
  field_simp
  simp
end GlobalTheory.CompanionTheory.SW.SdChange
