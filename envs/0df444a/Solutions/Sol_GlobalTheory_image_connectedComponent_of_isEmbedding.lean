-- Prove2me | solution 1 for GlobalTheory.image_connectedComponent_of_isEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:38.569018+00:00
-- url     : https://prove2.me/submissions/ee36a046-16e7-404d-9d22-7f10981cb5b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullback

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
theorem _root_.solution {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : Topology.IsEmbedding q) (a : A) :
    q '' connectedComponent a = connectedComponentIn (Set.range q) (q a) := by
  apply Set.Subset.antisymm
  · exact (isPreconnected_connectedComponent.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨a, mem_connectedComponent, rfl⟩ (Set.image_subset_range _ _)
  · intro x hx
    have hsub : connectedComponentIn (Set.range q) (q a) ⊆ Set.range q := connectedComponentIn_subset _ _
    have himg : q '' (q ⁻¹' connectedComponentIn (Set.range q) (q a)) = connectedComponentIn (Set.range q) (q a) :=
      Set.image_preimage_eq_of_subset hsub
    have hpc : IsPreconnected (q ⁻¹' connectedComponentIn (Set.range q) (q a)) := by
      rw [← hq.isInducing.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    have hS : q ⁻¹' connectedComponentIn (Set.range q) (q a) ⊆ connectedComponent a :=
      hpc.subset_connectedComponent (mem_connectedComponentIn ⟨a, rfl⟩)
    rw [← himg] at hx
    exact Set.image_mono hS hx
end GlobalTheory
