-- Prove2me | solution 1 for MeasureTheory.not_isUniversallyNull_univ_cantor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:38.444243+00:00
-- url     : https://prove2.me/submissions/3c458164-5d7a-4e2d-867d-3c6dca17906a

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
namespace MeasureTheory
theorem _root_.solution : ¬ IsUniversallyNull (Set.univ : Set (ℕ → Bool)) :=
  fun h ↦ by simpa using h cantorMeasure
end MeasureTheory
