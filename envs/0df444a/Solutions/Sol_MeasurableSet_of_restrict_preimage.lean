-- Prove2me | solution 1 for MeasurableSet.of_restrict_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:02.831334+00:00
-- url     : https://prove2.me/submissions/2d4b5209-c00f-43d0-b325-b858412cac91

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
namespace MeasurableSet
theorem _root_.solution {ι β : Type*} [MeasurableSpace β]
    {s : Set ι} {T : Set (s → β)} (hT : (s.restrict ⁻¹' T : Set (ι → β)).Nonempty)
    (h : MeasurableSet (s.restrict ⁻¹' T : Set (ι → β))) :
    MeasurableSet T := by
  obtain ⟨x, -⟩ := hT
  classical
  let g (f : s → β) (y : ι) : β := if hy : y ∈ s then f ⟨y, hy⟩ else x y
  have hg : Measurable (fun f y ↦ if hy : y ∈ s then f ⟨y, hy⟩ else x y : (s → β) → _) :=
    measurable_pi_lambda _ (fun i ↦ by split <;> fun_prop)
  convert h.preimage hg
  ext i
  simp [Set.restrict, Set.domRestrict]
end MeasurableSet
