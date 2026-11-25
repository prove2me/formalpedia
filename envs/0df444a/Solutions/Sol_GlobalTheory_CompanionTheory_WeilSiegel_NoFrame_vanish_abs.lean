-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.vanish_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:52.148701+00:00
-- url     : https://prove2.me/submissions/e5ef8814-f65d-440b-9c09-6fb18ec321dc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
theorem _root_.solution {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] (e : X → X → ℂ)
    (he : ∀ z, Continuous fun v => e v z) (he' : ∀ v, Continuous fun z => e v z)
    (hen : ∀ a b, ‖e a b‖ = 1) (J : X → ℂ) (hJ : Integrable J μ) (N : Set X) (hN : IsOpen N)
    (hb : ∀ N' : Set X, IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : X → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, J v * e v z ∂μ) * Φ z ∂μ = 0) (z₀ : X) (hz : z₀ ∈ closure N) :
    ∫ v, J v * e v z₀ ∂μ = 0 := by
  have hbd : ∀ z, ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v‖ ∂μ := by
    intro z
    calc ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v * e v z‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ v, ‖J v‖ ∂μ := by
        congr 1
        ext v
        rw [norm_mul, hen, mul_one]
  have hFc : Continuous fun z => ∫ v, J v * e v z ∂μ := by
    refine continuous_of_dominated (F := fun z v => J v * e v z) (bound := fun v => ‖J v‖)
      (fun z => hJ.1.mul (he z).aestronglyMeasurable) (fun z => Filter.Eventually.of_forall
        fun v => by rw [norm_mul, hen, mul_one]) hJ.norm
      (Filter.Eventually.of_forall fun v => continuous_const.mul (he' v))
  set F : X → ℂ := fun z => ∫ v, J v * e v z ∂μ with hFdef
  have hzero : ∀ z₁ ∈ N, F z₁ = 0 := by
    intro z₁ hz₁
    by_contra hc
    set c := F z₁ with hcdef
    let G : X → ℝ := fun z => (starRingEnd ℂ c * F z).re
    have hGc : Continuous G := Complex.continuous_re.comp (continuous_const.mul hFc)
    have hG1 : 0 < G z₁ := by
      show 0 < (starRingEnd ℂ c * c).re
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hc
    have hN'o : IsOpen (N ∩ {z | 0 < G z}) := hN.inter (isOpen_lt continuous_const hGc)
    obtain ⟨Φ, hΦc, hΦi, hΦpos, hΦsupp, hΦ1, hint⟩ :=
      hb _ hN'o Set.inter_subset_left z₁ ⟨hz₁, hG1⟩
    have hint' : ∫ z, F z * Φ z ∂μ = 0 := hint
    have hFΦi : Integrable (fun z => F z * Φ z) μ := by
      refine Integrable.mono (hΦi.norm.const_mul (∫ v, ‖J v‖ ∂μ))
        (hFc.aestronglyMeasurable.mul hΦi.1) (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_norm,
        abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hbd z) (norm_nonneg _)
    let H : X → ℝ := fun z => (starRingEnd ℂ c * (F z * Φ z)).re
    have hHeq : ∀ z, H z = G z * (Φ z).re := by
      intro z
      simp only [H, G]
      rw [← mul_assoc, Complex.mul_re, (hΦpos z).2, mul_zero, sub_zero]
    have hHnn : ∀ z, 0 ≤ H z := by
      intro z
      rw [hHeq]
      by_cases hz : z ∈ N ∩ {z | 0 < G z}
      · exact mul_nonneg hz.2.le (hΦpos z).1
      · rw [hΦsupp z hz]
        simp
    have hHc : Continuous H := Complex.continuous_re.comp (continuous_const.mul (hFc.mul hΦc))
    have hHi : Integrable H μ := (hFΦi.const_mul (starRingEnd ℂ c)).re
    have hHpos : 0 < ∫ z, H z ∂μ := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hHnn z) hHi]
      apply hHc.isOpen_support.measure_pos μ
      refine ⟨z₁, ?_⟩
      rw [Function.mem_support, hHeq]
      exact (mul_pos hG1 hΦ1).ne'
    have hHzero : ∫ z, H z ∂μ = 0 := by
      have h : ∫ z, H z ∂μ = (∫ z, starRingEnd ℂ c * (F z * Φ z) ∂μ).re :=
        integral_re (hFΦi.const_mul _)
      rw [h, integral_const_mul, hint', mul_zero, Complex.zero_re]
    linarith
  exact closure_minimal hzero (isClosed_eq hFc continuous_const) hz
end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
