-- Prove2me | solution 1 for MeasureTheory.lintegral_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:42.326829+00:00
-- url     : https://prove2.me/submissions/437d7477-8122-428e-9342-5a14cfd24215

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable

set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]
namespace MeasureTheory
theorem _root_.solution (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] :
    ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  simp_rw [lintegral_countable', mul_comm]
end MeasureTheory
