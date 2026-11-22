-- Prove2me | solution 1 for MeasureTheory.measureReal_preimage_snd_singleton_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:31.913801+00:00
-- url     : https://prove2.me/submissions/328a2d79-9144-4dfc-ab7e-00a212bd0c44

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
theorem _root_.solution [Fintype Ω] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (y : Ω') :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : Ω, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  simp_all
end MeasureTheory
