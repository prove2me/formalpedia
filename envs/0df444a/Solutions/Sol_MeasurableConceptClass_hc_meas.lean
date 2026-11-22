-- Prove2me | solution 1 for MeasurableConceptClass.hc_meas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:35:19.997806+00:00
-- url     : https://prove2.me/submissions/f5ea443d-86a5-4326-9674-524fcf33b45b

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability

set_option autoImplicit true
@[expose] public section
public section
universe u
namespace MeasurableConceptClass
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c : Concept X Bool, Measurable c :=
  h.all_measurable
end MeasurableConceptClass
