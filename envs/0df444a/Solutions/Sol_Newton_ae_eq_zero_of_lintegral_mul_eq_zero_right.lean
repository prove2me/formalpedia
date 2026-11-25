-- Prove2me | solution 1 for Newton.ae_eq_zero_of_lintegral_mul_eq_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:09:14.650005+00:00
-- url     : https://prove2.me/submissions/23d5c873-422a-440a-9897-911960506aff

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Theorems.Thm_Newton_ae_eq_zero_of_lintegral_mul_eq_zero_left

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞}
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (h_int : ∫⁻ x, f x * g x ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  -- Apply the left version with the roles of `f` and `g` swapped.
  have h_int' : ∫⁻ x, g x * f x ∂μ = 0 := by
    simpa [mul_comm] using h_int
  simpa [mul_comm] using
    (ae_eq_zero_of_lintegral_mul_eq_zero_left
      (μ := μ) (f := g) (g := f) hf_pos hg_meas hf_meas h_int')
end Newton
