-- Prove2me | solution 1 for Newton.tonelli_nonneg_prod_eq_iterated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:50.494738+00:00
-- url     : https://prove2.me/submissions/f3d08d86-ffa0-4de9-b03f-fe86ead37125

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
variable [SFinite μ]
namespace Newton
theorem _root_.solution
    (f : G × G → ℝ≥0∞)
    (hf_meas : Measurable f) :
    ∫⁻ p, f p ∂(μ.prod μ) = ∫⁻ x, ∫⁻ y, f (x, y) ∂μ ∂μ := by
  simpa using lintegral_prod (μ := μ) (ν := μ) f hf_meas.aemeasurable
end Newton
