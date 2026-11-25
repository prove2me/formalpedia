-- Prove2me | solution 1 for Newton.tonelli_norm_convolution_section_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:05:10.101363+00:00
-- url     : https://prove2.me/submissions/6f96428a-e8e9-43de-801e-da72d74339db

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
variable [AddCommGroup G]
namespace Newton
theorem _root_.solution
    {f g : G → ℂ} [SFinite μ]
    (h_kernel_int : Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ)) :
    ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖ * ‖g y‖) μ := by
  have h_sections :
      ∀ᵐ x ∂μ, Integrable (fun y : G => f (x - y) * g y) μ :=
    (Integrable.prod_right_ae (μ := μ) (ν := μ) h_kernel_int)
  refine h_sections.mono ?_
  intro x hx
  simpa [norm_mul] using hx.norm
end Newton
