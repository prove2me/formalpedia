-- Prove2me | solution 1 for Newton.tonelli_product_ae_section_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:07.176427+00:00
-- url     : https://prove2.me/submissions/606e1e26-d097-4c9b-a349-499e5b97c553

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
variable [SFinite μ]
namespace Newton
theorem _root_.solution
    {f g : G → ℝ≥0∞}
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (hf_int : ∫⁻ x, f x ∂μ < ∞)
    (hg_int : ∫⁻ y, g y ∂μ < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f x * g y ∂μ < ∞ := by
  have h_prod_meas :
      Measurable fun p : G × G => f p.1 * g p.2 :=
    (hf_meas.comp measurable_fst).mul (hg_meas.comp measurable_snd)
  have h_prod_eq :
      ∫⁻ p : G × G, f p.1 * g p.2 ∂(μ.prod μ)
        = (∫⁻ x, f x ∂μ) * (∫⁻ y, g y ∂μ) := by
    simpa using
      lintegral_prod_mul (μ := μ) (ν := μ)
        (f := f) (g := g)
        hf_meas.aemeasurable hg_meas.aemeasurable
  have h_prod_int :
      ∫⁻ p : G × G, f p.1 * g p.2 ∂(μ.prod μ) < ∞ := by
    simpa [h_prod_eq] using ENNReal.mul_lt_top hf_int hg_int
  exact tonelli_ae_section_lt_top (μ := μ) h_prod_meas h_prod_int
end Newton
