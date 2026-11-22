-- Prove2me | solution 1 for MeasureTheory.Measure.map_eval_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:38.114142+00:00
-- url     : https://prove2.me/submissions/13608759-8ea8-48dd-90e5-b9fa89c6ecaf

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage

set_option autoImplicit true
@[expose] public section
public section
open Function Set
open MeasureTheory MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
namespace MeasureTheory.Measure
theorem _root_.solution (i : ι) : Measure.map (eval i) (Measure.pi μ) = μ i := by
  ext s hs
  simp_rw [Measure.map_apply (measurable_pi_apply i) hs, pi_eval_preimage]
end MeasureTheory.Measure
