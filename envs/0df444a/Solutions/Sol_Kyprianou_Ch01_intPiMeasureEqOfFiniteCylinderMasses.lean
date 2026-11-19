-- Prove2me | solution 1 for Kyprianou.Ch01.intPiMeasureEqOfFiniteCylinderMasses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:19:17.255844+00:00
-- url     : https://prove2.me/submissions/7a5036af-ea21-4833-9e98-37a530156a89

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.IdentDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Finite cylinder masses determine a finite integer-valued product measure. -/
theorem solution
    {ι : Type*} (μ ν : Measure (ι → ℤ))
    (hFinite : μ Set.univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℤ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      μ (Set.pi (J : Set ι) B) = ν (Set.pi (J : Set ι) B)) :
    μ = ν := by
  have huniv : μ Set.univ = ν Set.univ := by
    simpa using hCyl ∅ (fun _ => Set.univ) (by simp)
  haveI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hFinite⟩
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders
      (fun i => MeasurableSpace.isPiSystem_measurableSet)
      (fun i => (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℤ))))
    ?_ huniv
  rintro S ⟨J, B, hB, rfl⟩
  exact hCyl J B fun i _ => hB i (Set.mem_univ i)
