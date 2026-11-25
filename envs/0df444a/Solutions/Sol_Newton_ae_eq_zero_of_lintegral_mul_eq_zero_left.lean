-- Prove2me | solution 1 for Newton.ae_eq_zero_of_lintegral_mul_eq_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:52.734096+00:00
-- url     : https://prove2.me/submissions/f6998e3f-1bef-4509-95b9-e04a9081a7cb

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Theorems.Thm_Newton_lintegral_eq_zero_iff_ae_eq_zero

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞}
    (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (h_int : ∫⁻ x, f x * g x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  -- First show that `f * g` vanishes a.e. from the vanishing of its integral.
  have h_fg_meas : AEMeasurable (fun x => f x * g x) μ := hf_meas.mul hg_meas
  have h_fg_zero : (fun x => f x * g x) =ᵐ[μ] 0 :=
    (lintegral_eq_zero_iff_ae_eq_zero (α := α) (μ := μ)
        (f := fun x => f x * g x) h_fg_meas).1 h_int
  -- Use the positivity of `g` to deduce that `f` itself vanishes a.e.
  refine (hg_pos.and h_fg_zero).mono ?_
  intro x hx
  rcases hx with ⟨hg_pos_x, hfg_zero_x⟩
  -- Pointwise lemma: if `0 < g x` and `f x * g x = 0`, then `f x = 0`.
  have hg_ne_zero : g x ≠ 0 := (ne_of_gt hg_pos_x)
  -- We split according to whether `g x` is infinite or finite.
  by_cases hxg_top : g x = ⊤
  · -- Case `g x = ∞`.
    -- Then `f x * ∞ = 0`, which forces `f x = 0`.
    have h' : f x * (∞ : ℝ≥0∞) = 0 := by simpa [hxg_top] using hfg_zero_x
    -- Analyze using `ENNReal.mul_top'`.
    by_contra hfx_ne
    have h_if : (if f x = 0 then 0 else (∞ : ℝ≥0∞)) = (0 : ℝ≥0∞) := by
      simpa [ENNReal.mul_top'] using h'
    have h_fx_zero : f x = 0 := by simpa [hfx_ne] using h_if
    exact hfx_ne h_fx_zero
  · -- Case `g x` is finite (not `∞`).
    have hg_ne_top : g x ≠ (∞ : ℝ≥0∞) := hxg_top
    -- Multiply the equality `f x * g x = 0` by `(g x)⁻¹` on the right.
    have h' : f x * g x = 0 := hfg_zero_x
    have h_mul := congrArg (fun y => y * (g x)⁻¹) h'
    -- Simplify using associativity and `mul_inv_cancel`.
    have : f x = 0 := by
      simpa [mul_assoc, ENNReal.mul_inv_cancel hg_ne_zero hg_ne_top] using h_mul
    exact this
end Newton
