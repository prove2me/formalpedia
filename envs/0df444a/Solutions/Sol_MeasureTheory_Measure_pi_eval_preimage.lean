-- Prove2me | solution 1 for MeasureTheory.Measure.pi_eval_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:27.585638+00:00
-- url     : https://prove2.me/submissions/fb4e1b82-28a5-4977-abdc-7e5aad5fe008

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi

set_option autoImplicit true
@[expose] public section
public section
open Function Set
open MeasureTheory MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
namespace MeasureTheory.Measure
theorem _root_.solution (i : ι) (s : Set (α i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by
  classical
  simp_rw [eval_preimage, pi_pi, apply_update (fun i ↦ μ i), measure_univ,
    Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const_one, mul_one]
end MeasureTheory.Measure
