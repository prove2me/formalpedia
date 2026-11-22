-- Prove2me | solution 1 for MeasureTheory.lintegral_eq_setLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:17.36839+00:00
-- url     : https://prove2.me/submissions/85828be1-221c-459f-bd27-e6ccf0d0ee54

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic

set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
namespace MeasureTheory
theorem _root_.solution (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]
end MeasureTheory
