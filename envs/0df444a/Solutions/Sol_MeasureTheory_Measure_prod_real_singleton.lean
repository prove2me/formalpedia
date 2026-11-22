-- Prove2me | solution 1 for MeasureTheory.Measure.prod_real_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:22.731448+00:00
-- url     : https://prove2.me/submissions/b1147ecb-9771-48e0-9d3b-038d25e76cb5

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Theorems.Thm_MeasureTheory_Measure_prod_apply_singleton


set_option autoImplicit true
@[expose] public section
public section
open Function Set
open scoped ENNReal NNReal
open MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}
namespace MeasureTheory
namespace _root_.MeasureTheory.Measure
theorem _root_.solution
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x :
  α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, Measure.prod_apply_singleton]
end _root_.MeasureTheory.Measure
end MeasureTheory
