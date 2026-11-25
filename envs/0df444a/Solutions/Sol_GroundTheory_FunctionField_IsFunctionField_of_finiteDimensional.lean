-- Prove2me | solution 1 for GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:14.36377+00:00
-- url     : https://prove2.me/submissions/56d56be5-0fe2-4599-8452-686b69076ce6

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
namespace _root_.GroundTheory.FunctionField.IsFunctionField
theorem _root_.solution [IsFunctionField k K]
    [FiniteDimensional K K'] : IsFunctionField k K' := by
  obtain ⟨y, hy, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hb := (isTranscendenceBasis_singleton hy hfin).algebraMap_comp (A := K')
  have hr : Set.range (⇑(algebraMap K K') ∘ ((↑) : ({y} : Set K) → K)) = {algebraMap K K' y} := by
    rw [Set.range_comp, Subtype.range_coe, Set.image_singleton]
  have halg := hb.isAlgebraic_field
  rw [hr] at halg
  have := essFiniteType (k := k) (K := K)
  have : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {algebraMap K K' y}) K' :=
    Algebra.EssFiniteType.of_comp k _ K'
  exact ⟨⟨algebraMap K K' y,
    (algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).1 hb.1,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩
end _root_.GroundTheory.FunctionField.IsFunctionField
end GroundTheory.FunctionField.Place
