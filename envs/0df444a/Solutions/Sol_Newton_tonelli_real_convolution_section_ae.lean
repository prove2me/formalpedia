-- Prove2me | solution 1 for Newton.tonelli_real_convolution_section_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:05:38.612845+00:00
-- url     : https://prove2.me/submissions/0889fba2-9e9d-428a-b360-0dadb551883b

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
variable [AddCommGroup G]
namespace Newton
theorem _root_.solution
    {f g : G → ℝ} [MeasurableSub₂ G] [SFinite μ]
    (hf_meas : Measurable f)
    (hg_meas : Measurable g)
    (h_kernel_int : ∫⁻ p, ENNReal.ofReal (|f (p.1 - p.2)| * |g p.2|) ∂(μ.prod μ) < ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (|f (x - y)| * |g y|) ∂μ < ∞ := by
  set F : G × G → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (|f (p.1 - p.2)| * |g p.2|)
  have hF_meas : Measurable F := by
    have hf_comp : Measurable fun p : G × G => f (p.1 - p.2) :=
      hf_meas.comp measurable_sub
    have hf_abs : Measurable fun p : G × G => |f (p.1 - p.2)| :=
      (continuous_abs.measurable.comp hf_comp)
    have hg_comp : Measurable fun p : G × G => g p.2 :=
      hg_meas.comp measurable_snd
    have hg_abs : Measurable fun p : G × G => |g p.2| :=
      (continuous_abs.measurable.comp hg_comp)
    have h_mul :
        Measurable fun p : G × G => |f (p.1 - p.2)| * |g p.2| :=
      hf_abs.mul hg_abs
    exact ENNReal.measurable_ofReal.comp h_mul
  simpa [F] using
    tonelli_ae_section_lt_top (μ := μ) (f := F) hF_meas h_kernel_int
end Newton
