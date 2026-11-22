-- Prove2me | solution 1 for MeasurableConceptClass.hWB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:35:19.550931+00:00
-- url     : https://prove2.me/submissions/40371d08-b5c2-4a91-a872-49a7544757c3

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
    WellBehavedVC X C :=
  h.wellBehaved
end MeasurableConceptClass
