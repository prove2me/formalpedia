-- Prove2me | solution 1 for GlobalTheory.HomExt.exists_lift_of_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:54.285019+00:00
-- url     : https://prove2.me/submissions/257ae059-e2af-441f-b986-b08e429b2cf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfDensePartOfIsIntegral
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.HomExt
namespace GlobalTheory.HomExt
theorem _root_.solution {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (x : T ⟶ X) (h : Set.range x ⊆ Set.range j) : ∃ y : T ⟶ U, y ≫ j = x := by
  have hs : Function.Surjective (pullback.fst x j) := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    exact fun t ↦ h ⟨t, rfl⟩
  have hp : IsPreimmersion (pullback.fst x j) := inferInstance
  have : IsIso (pullback.fst x j) := by
    rw [isIso_iff_isIso_stalkMap]
    refine ⟨?_, isIso_stalkMap_of_flat_of_surjectiveOnStalks _⟩
    exact TopCat.isIso_of_bijective_of_isOpenMap _ ⟨hp.isEmbedding.injective, hs⟩
      (hp.isEmbedding.isInducing.isOpenMap (by rw [hs.range_eq]; exact isOpen_univ))
  exact ⟨inv (pullback.fst x j) ≫ pullback.snd x j, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩
end GlobalTheory.HomExt
