-- Prove2me | solution 1 for MeasureTheory.measureReal_preimage_fst_singleton_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:25.93184+00:00
-- url     : https://prove2.me/submissions/8b528735-657d-4fff-a253-a75bf239091e

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real

set_option autoImplicit true
@[expose] public section
public section
open Function Set
open scoped ENNReal NNReal
open MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}
variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']
namespace MeasureTheory
theorem _root_.solution [Fintype Ω'] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (x : Ω) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : Ω', μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  simp_all
end MeasureTheory
