-- Prove2me | solution 1 for MeasureTheory.analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4d323981-46a3-5ca6-aaf8-397f97e90ed2

import Mathlib
import Theorems.Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at

set_option autoImplicit false

open MeasureTheory

theorem solution
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y)
    (a : ℝ) (F : ℂ → Y → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ)
    (hhol : ∀ y : Y, Differentiable ℂ (fun s => F s y))
    (hdom : ∀ s₀ : ℂ, a < s₀.re → ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M μ ∧
      ∀ s ∈ Metric.ball s₀ ε, ∀ y : Y, ‖F s y‖ ≤ M y)
    (hreal : ∀ σ : ℝ, a < σ → ∀ y : Y, (F σ y).im = 0 ∧ 0 ≤ (F σ y).re)
    (hcont : ∀ σ : ℝ, a < σ → Continuous (F σ))
    (y₀ : Y) (hpt : ∀ σ : ℝ, a < σ → 0 < (F σ y₀).re)
    (hopen : ∀ U : Set Y, IsOpen U → y₀ ∈ U → 0 < μ U) :
    (∀ s : ℂ, a < s.re → Integrable (F s) μ) ∧
      AnalyticOnNhd ℂ (fun s : ℂ => ∫ y, F s y ∂μ) {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ → (∫ y, F σ y ∂μ).im = 0 ∧ 0 < (∫ y, F σ y ∂μ).re) := by
  have hint : ∀ s : ℂ, a < s.re → Integrable (F s) μ := by
    intro s hs
    obtain ⟨ε, hε, M, hM, hbd⟩ := hdom s hs
    exact Integrable.mono' hM (hmeas s)
      (Filter.Eventually.of_forall fun y => hbd s (Metric.mem_ball_self hε) y)
  have hopenU : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∫ y, F s y ∂μ) {s : ℂ | a < s.re} :=
    MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le μ hopenU F
      (fun s _ => hmeas s) (fun y => (hhol y).differentiableOn) (fun s₀ hs₀ => hdom s₀ hs₀)
  refine ⟨hint, hdiff.analyticOnNhd hopenU, ?_⟩
  intro σ hσ
  have hσ' : a < (σ : ℂ).re := by simpa using hσ
  have hI : Integrable (F σ) μ := hint σ hσ'
  refine ⟨?_, ?_⟩
  ·
    have h1 : (∫ y, F σ y ∂μ).im = ∫ y, (F σ y).im ∂μ := by
      have h := integral_im hI
      simpa using h.symm
    rw [h1]
    have h2 : (fun y => (F (σ : ℂ) y).im) = fun _ => (0 : ℝ) := funext fun y => (hreal σ hσ y).1
    rw [h2, integral_zero]
  ·
    have h1 : (∫ y, F σ y ∂μ).re = ∫ y, (F σ y).re ∂μ := by
      have h := integral_re hI
      simpa using h.symm
    rw [h1]
    have hnn : 0 ≤ᵐ[μ] fun y => (F (σ : ℂ) y).re :=
      Filter.Eventually.of_forall fun y => (hreal σ hσ y).2
    have hIre : Integrable (fun y => (F (σ : ℂ) y).re) μ := hI.re
    rw [integral_pos_iff_support_of_nonneg_ae hnn hIre]
    have hsub : (fun y => (F (σ : ℂ) y).re) ⁻¹' Set.Ioi 0 ⊆ Function.support fun y => (F (σ : ℂ) y).re :=
      fun y hy => ne_of_gt hy
    have hop : IsOpen ((fun y => (F (σ : ℂ) y).re) ⁻¹' Set.Ioi 0) :=
      isOpen_Ioi.preimage (Complex.continuous_re.comp (hcont σ hσ))
    exact lt_of_lt_of_le (hopen _ hop (hpt σ hσ)) (measure_mono hsub)

#print axioms solution

end S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at
end P2MW
export P2MW.S_MeasureTheory_analyticOnNhd_integral_and_im_eq_zero_and_re_pos_of_locally_norm_le_of_re_pos_at (solution)
