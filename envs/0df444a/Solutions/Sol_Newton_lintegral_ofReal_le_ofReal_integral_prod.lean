-- Prove2me | solution 1 for Newton.lintegral_ofReal_le_ofReal_integral_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:09.974344+00:00
-- url     : https://prove2.me/submissions/04500418-4ecb-4530-a159-5fd757b21a60

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Theorems.Thm_Newton_lintegral_ofReal_eq_ofReal_integral_prod

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_lt_top : ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ⊤) :
    ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) ≤
      ENNReal.ofReal (∫ x, ∫ y, H (x, y) ∂μ ∂μ) := by
  -- Since lintegral is finite, H is integrable, so we can use equality
  -- For nonneg functions, finite lintegral of ofReal implies integrability
  have h_norm_eq : ∀ p, ENNReal.ofReal (H p) = ENNReal.ofReal ‖H p‖ := by
    intro p
    have h_nonneg : 0 ≤ H p := hH_nonneg p
    simp [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
  have h_lt_top' : ∫⁻ p, ENNReal.ofReal ‖H p‖ ∂(μ.prod μ) < ⊤ := by
    simp_rw [← h_norm_eq]
    exact hH_lt_top
  -- Convert to HasFiniteIntegral
  have h_enorm_eq : ∀ p, ENNReal.ofReal ‖H p‖ = ‖H p‖ₑ := by
    intro p
    exact ofReal_norm_eq_enorm (H p)
  have h_finite : HasFiniteIntegral H (μ.prod μ) := by
    simp only [HasFiniteIntegral]
    simp_rw [h_enorm_eq] at h_lt_top'
    exact h_lt_top'
  have hH_int : Integrable H (μ.prod μ) :=
    ⟨hH_aemeas.aestronglyMeasurable, h_finite⟩
  rw [lintegral_ofReal_eq_ofReal_integral_prod μ hH_nonneg hH_int]
end Newton
