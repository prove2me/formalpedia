-- Prove2me | solution 1 for MeasureTheory.Measure.ext_of_initialCylinders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:10.053537+00:00
-- url     : https://prove2.me/submissions/81de2cb8-77d3-4d18-96c3-cf0b0cce7732

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_InitialCylinder
public import Theorems.Thm_MeasureTheory_isPiSystem_initialCylinders
public import Theorems.Thm_MeasureTheory_generateFrom_initialCylinders
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
namespace Measure
theorem _root_.solution {μ ν : Measure (ℕ → Bool)} [IsFiniteMeasure μ]
    (h : ∀ (n : ℕ) (v : ℕ → Bool),
      μ (cylinderOn (Finset.range n) v) = ν (cylinderOn (Finset.range n) v)) : μ = ν :=
  ext_of_generate_finite _ generateFrom_initialCylinders isPiSystem_initialCylinders
    (by rintro _ ⟨n, v, rfl⟩; exact h n v) (by simpa [cylinderOn] using h 0 fun _ ↦ false)
end Measure
end MeasureTheory
