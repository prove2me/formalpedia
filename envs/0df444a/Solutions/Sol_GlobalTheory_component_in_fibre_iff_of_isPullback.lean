-- Prove2me | solution 1 for GlobalTheory.component_in_fibre_iff_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:08:39.673804+00:00
-- url     : https://prove2.me/submissions/ad7c4a22-a752-4cc4-8727-d70b66e9cb10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullback
import Theorems.Thm_GlobalTheory_image_connectedComponent_of_isEmbedding

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
theorem _root_.solution :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s))
      (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s →
      ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  intro X S f e s Y g q y₀ hP h0 y
  haveI : IsPreimmersion q :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hP.flip inferInstance
  have hq : Topology.IsEmbedding q := q.isEmbedding
  have hr : Set.range q = f ⁻¹' {s} := by
    have h1 : Set.range q = Set.range (pullback.fst f (S.fromSpecResidueField s)) := by
      rw [← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr, Set.image_univ]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hP.isoPullback)).surjective
    rw [h1, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [← h0, ← hr, ← image_connectedComponent_of_isEmbedding hq]
  exact hq.injective.mem_set_image
end GlobalTheory
