-- Prove2me | solution 1 for MeasureTheory.setLIntegral_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:20.007583+00:00
-- url     : https://prove2.me/submissions/09670d84-85f7-49f3-94be-c375b8b1293e

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
theorem _root_.solution (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by
  simp_rw [mul_comm, lintegral_finset]
end MeasureTheory
