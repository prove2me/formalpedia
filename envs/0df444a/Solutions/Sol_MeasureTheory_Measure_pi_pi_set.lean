-- Prove2me | solution 1 for MeasureTheory.Measure.pi_pi_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:27.077686+00:00
-- url     : https://prove2.me/submissions/8a51ef19-10e8-4b4f-ad63-b5e81d7f0581

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
theorem _root_.solution (t : Set ι) [DecidablePred (· ∈ t)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ Finset.univ.filter (· ∈ t), μ i (s i) := by
  classical
  simp (config := {singlePass := true}) only [← pi_univ_ite]
  simp_rw [pi_pi, apply_ite, measure_univ,
    Finset.prod_ite, Finset.prod_const_one, mul_one]
end MeasureTheory.Measure
