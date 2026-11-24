-- Prove2me | solution 1 for GlobalTheory.FoldIntegral.fold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:21.207157+00:00
-- url     : https://prove2.me/submissions/08e45424-f885-4d45-993d-5770268cb8be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralFoldViaLintegralFormula
import Theorems.Thm_GlobalTheory_FoldIntegral_integral_integral_eq_pos_sub_neg
import Theorems.Thm_GlobalTheory_FoldIntegral_clm_integral_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.FoldIntegral
namespace GlobalTheory.FoldIntegral
theorem _root_.solution : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  intro α Y Z _ _ _ μ Fs ν m S hS Φ hΦ c hc P hQ G hG hP hfin
  haveI : IsFiniteMeasure (m.restrict S) := ⟨by simpa using hS⟩
  have hint : IntegrableOn G Fs μ := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hQ _ hG.enorm (hP (fun z => ‖z‖ₑ) (by simp))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hint, ?_⟩
  have hH : Measurable fun p : Y × Z => G (Φ p.1 p.2) := hG.comp hΦ
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ z, ‖L z‖ ≤ ‖z‖) →
      L (∫ x in Fs, G x ∂μ) = c * L (∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν) := by
    intro L hL
    have hLm : Measurable L := L.continuous.measurable
    have h1 := clm_integral_integral ν (m.restrict S) _ hH hfin L
    have h2 := integral_integral_eq_pos_sub_neg ν (m.restrict S)
      (fun p : Y × Z => L (G (Φ p.1 p.2))) (hLm.comp hH)
      (lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hL _)) hfin)
    have h3 := hQ (fun x => ENNReal.ofReal (L (G x))) (hLm.comp hG).ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (L z)) (by simp))
    have h4 := hQ (fun x => ENNReal.ofReal (-L (G x))) (hLm.comp hG).neg.ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (-L z)) (by simp))
    simp only at h1 h2
    rw [h1, h2, ← L.integral_comp_comm hint,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hint), h3, h4,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, mul_sub]
  apply Complex.ext
  · have := key Complex.reCLM (fun z => by simpa using Complex.abs_re_le_norm z)
    simpa using this
  · have := key Complex.imCLM (fun z => by simpa using Complex.abs_im_le_norm z)
    simpa using this
end GlobalTheory.FoldIntegral
