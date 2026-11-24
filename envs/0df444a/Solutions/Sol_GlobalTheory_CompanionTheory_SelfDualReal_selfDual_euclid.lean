-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualReal.selfDual_euclid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:08.778802+00:00
-- url     : https://prove2.me/submissions/5e8e154d-1bef-4944-8af5-9b68b29f2fdf

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualReal
namespace GlobalTheory.CompanionTheory.SelfDualReal
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (S : W →ₗ[ℝ] W)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hd : LinearMap.det S ≠ 0) :
    ∃ ν : Measure W, SelfDual ν
      (fun x y => Complex.exp (((-2 * Real.pi * ⟪x, S y⟫ : ℝ) : ℂ) * Complex.I)) := by
  set d : ℝ := |LinearMap.det S| with hdd
  have hd0 : 0 < d := abs_pos.mpr hd
  set c : ℝ := Real.sqrt d with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hd0
  have hcc : c * c = d := Real.mul_self_sqrt hd0.le
  have hne : ENNReal.ofReal c ≠ 0 := by simpa using hc0
  refine ⟨ENNReal.ofReal c • volume,
    Measure.IsAddHaarMeasure.smul volume hne ENNReal.ofReal_ne_top, ?_⟩
  intro Φ hΦ hcs hi z
  have hΦi : Integrable Φ := hΦ.integrable_of_hasCompactSupport hcs
  have hF : ∀ y, ∫ x, Φ x * Complex.exp (((-2 * Real.pi * ⟪x, S y⟫ : ℝ) : ℂ) * Complex.I)
      = 𝓕 Φ (S y) := by
    intro y
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
  let L : W ≃L[ℝ] W := (S.equivOfDetNeZero hd).toContinuousLinearEquiv
  have hm : MeasurableEmbedding S := L.toHomeomorph.measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure W) hd
  have hne' : ENNReal.ofReal |(LinearMap.det S)⁻¹| ≠ 0 := by simpa using hd
  simp only [integral_smul_measure, hF, ENNReal.toReal_ofReal hc0.le] at hi ⊢
  rw [integrable_smul_measure hne ENNReal.ofReal_ne_top] at hi
  have hi2 : Integrable (fun y => 𝓕 Φ (S y)) := by
    have := hi.smul c⁻¹
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [smul_smul, hc0.ne']
  have hi3 : Integrable (𝓕 Φ) := by
    have h1 : Integrable (𝓕 Φ) (Measure.map S volume) := hm.integrable_map_iff.mpr hi2
    rw [hmap, integrable_smul_measure hne' ENNReal.ofReal_ne_top] at h1
    exact h1
  have hinv := congrFun (hΦ.fourierInv_fourier_eq hΦi hi3) (-z)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, Real.fourier_eq'] at hinv
  have h3 := hm.integral_map (μ := volume)
    (fun w => Complex.exp (((-2 * Real.pi * ⟪w, z⟫ : ℝ) : ℂ) * Complex.I) • 𝓕 Φ w)
  rw [hmap, integral_smul_measure, hinv, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    ← hdd] at h3
  have h4 : ∫ y, (c • 𝓕 Φ (S y)) * Complex.exp (((-2 * Real.pi * ⟪y, S z⟫ : ℝ) : ℂ) * Complex.I)
      = c • (d⁻¹ • Φ (-z)) := by
    rw [h3, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hS, smul_eq_mul, smul_mul_assoc]
    rw [mul_comm]
  rw [h4, smul_smul, smul_smul, hcc, mul_inv_cancel₀ hd0.ne', one_smul]
end GlobalTheory.CompanionTheory.SelfDualReal
