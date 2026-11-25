-- Prove2me | solution 1 for GlobalTheory.IsGenericPointHom.quasiCompact_and_dominant_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:45.257121+00:00
-- url     : https://prove2.me/submissions/3400c71c-b87a-41a7-a2ee-303eec41dfa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_IsGenericPointHom_range_eq
import Theorems.Thm_GlobalTheory_IsGenericPointHom_isAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory
open ExtUnique
open GlobalTheory.IsGenericPointHom
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}
namespace GlobalTheory.IsGenericPointHom
theorem _root_.solution [IsLocallyNoetherian S] {V : Scheme.{u}} {k : U ⟶ V} {i : V ⟶ S}
    [IsOpenImmersion i] (hj : IsGenericPointHom (k ≫ i)) :
    QuasiCompact k ∧ IsSchemeTheoreticallyDominant k := by
  have : IsAffine U := hj.isAffine
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion i
  have : IsReduced V := isReduced_of_isOpenImmersion i
  have hdom : IsDominant k := by
    rw [isDominant_iff, DenseRange, i.isOpenEmbedding.isInducing.dense_iff]
    intro v
    have hr : i '' Set.range k = {genericPoint S} := by
      rw [← hj.range_eq, ← Set.range_comp]
      rfl
    have hη : closure {genericPoint S} = (⊤ : Set S) := genericPoint_spec S
    rw [hr, hη]
    trivial
  exact ⟨inferInstance, IsSchemeTheoreticallyDominant.of_isDominant k⟩
end GlobalTheory.IsGenericPointHom
