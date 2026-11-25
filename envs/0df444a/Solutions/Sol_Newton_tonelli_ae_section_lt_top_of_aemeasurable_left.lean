-- Prove2me | solution 1 for Newton.tonelli_ae_section_lt_top_of_aemeasurable_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:23:27.1508+00:00
-- url     : https://prove2.me/submissions/c66604fc-ba48-4f10-a2ff-eae0f811d80e

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Theorems.Thm_Newton_tonelli_ae_section_lt_top

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    [SFinite μ]
    {f : G × G → ℝ≥0∞}
    (hf_aemeas : AEMeasurable f (μ.prod μ))
    (hf_int : ∫⁻ p, f p ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ < ∞ := by
  -- Choose a measurable representative of f on μ.prod μ.
  set f0 : G × G → ℝ≥0∞ := hf_aemeas.mk f with hf0_def
  have hf0_meas : Measurable f0 := hf_aemeas.measurable_mk
  have hf_ae_eq : f =ᵐ[μ.prod μ] f0 := hf_aemeas.ae_eq_mk
  -- Transfer product finiteness along the a.e. equality.
  have hf0_int : ∫⁻ p, f0 p ∂(μ.prod μ) < ∞ := by
    have h_eq := lintegral_congr_ae hf_ae_eq
    simpa [h_eq] using hf_int
  -- Apply the measurable Tonelli consequence to f0.
  have h_left : ∀ᵐ x ∂μ, ∫⁻ y, f0 (x, y) ∂μ < ∞ :=
    tonelli_ae_section_lt_top (μ := μ) (f := f0) hf0_meas hf0_int
  -- Relate sections of f and f0 via the product a.e. equality.
  have h_curry :
      ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[μ] fun y => f0 (x, y) :=
    Measure.ae_ae_eq_curry_of_prod (μ := μ) (ν := μ) hf_ae_eq
  have h_eq_int :
      ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂μ = ∫⁻ y, f0 (x, y) ∂μ := by
    refine h_curry.mono ?_
    intro x hx
    simpa using lintegral_congr_ae hx
  -- Conclude finiteness for f by equality with the finite sections of f0.
  refine (h_eq_int.and h_left).mono ?_
  intro x hx
  rcases hx with ⟨h_eq, h_lt⟩
  simpa [h_eq] using h_lt
end Newton
