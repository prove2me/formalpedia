-- Prove2me | solution 1 for GlobalTheory.separated_of_isOpen_component_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:40.636979+00:00
-- url     : https://prove2.me/submissions/f2f416c4-4f7b-44d1-a029-7f25820b69e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartitionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Type*} [TopologicalSpace X] (F : Set X) (a : X)
    (ha : a ∈ F) (ho : IsOpen (connectedComponent (⟨a, ha⟩ : F))) :
    Disjoint (connectedComponentIn F a) (closure (F \ connectedComponentIn F a)) ∧
      Disjoint (closure (connectedComponentIn F a)) (F \ connectedComponentIn F a) := by
  have hC : connectedComponentIn F a = Subtype.val '' connectedComponent (⟨a, ha⟩ : F) :=
    connectedComponentIn_eq_image ha
  have hmem : ∀ y : F, (y : X) ∈ connectedComponentIn F a ↔ y ∈ connectedComponent (⟨a, ha⟩ : F) := by
    intro y
    rw [hC]
    exact Subtype.val_injective.mem_set_image
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 ho
  obtain ⟨Z, hZ, hZe⟩ := isClosed_induced_iff.1
    (isClosed_connectedComponent : IsClosed (connectedComponent (⟨a, ha⟩ : F)))
  constructor
  · have h1 : closure (F \ connectedComponentIn F a) ⊆ Uᶜ := by
      refine closure_minimal ?_ hU.isClosed_compl
      rintro y ⟨hyF, hy⟩ hyU
      apply hy
      refine (hmem ⟨y, hyF⟩).2 ?_
      rw [← hUe]
      exact hyU
    refine Set.disjoint_left.2 fun y hy hy' => h1 hy' ?_
    have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
    rw [← hUe] at this
    exact this
  · have h1 : closure (connectedComponentIn F a) ⊆ Z := by
      refine closure_minimal ?_ hZ
      intro y hy
      have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
      rw [← hZe] at this
      exact this
    refine Set.disjoint_left.2 fun y hy hy' => hy'.2 ?_
    refine (hmem ⟨y, hy'.1⟩).2 ?_
    rw [← hZe]
    exact h1 hy
end GlobalTheory
