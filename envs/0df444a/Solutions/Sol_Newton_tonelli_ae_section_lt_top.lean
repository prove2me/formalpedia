-- Prove2me | solution 1 for Newton.tonelli_ae_section_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:20:13.823791+00:00
-- url     : https://prove2.me/submissions/8f7b0bdc-2b1b-4523-b606-2fcf48a1ae82

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Theorems.Thm_Newton_tonelli_nonneg_prod_eq_iterated

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
variable [SFinite μ]
namespace Newton
theorem _root_.solution
    {f : G × G → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ < ∞ := by
  have h_prod_eq := tonelli_nonneg_prod_eq_iterated (μ := μ) f hf_meas
  rw [h_prod_eq] at hf_int
  have h_meas_section : Measurable fun x => ∫⁻ y, f (x, y) ∂μ :=
    Measurable.lintegral_prod_right' hf_meas
  exact ae_lt_top h_meas_section (ne_of_lt hf_int)
end Newton
