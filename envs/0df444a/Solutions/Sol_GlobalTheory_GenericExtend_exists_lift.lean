-- Prove2me | solution 1 for GlobalTheory.GenericExtend.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:06.528155+00:00
-- url     : https://prove2.me/submissions/1f5cb3e1-1441-41b3-b07c-dc62c46d918c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j] (g : T ⟶ X)
    (h : Set.range g ⊆ Set.range j) : ∃ κ : T ⟶ U, κ ≫ j = g := by
  have hs : Surjective (pullback.fst g j) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun t ↦ h ⟨t, rfl⟩⟩
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst g j)
  have : IsOpenImmersion (pullback.fst g j) :=
    IsOpenImmersion.of_isIso_stalkMap _ ⟨(pullback.fst g j).isEmbedding, by
      rw [(pullback.fst g j).surjective.range_eq]; exact isOpen_univ⟩
  have : IsIso (pullback.fst g j) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact ⟨inv (pullback.fst g j) ≫ pullback.snd g j, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩
end GlobalTheory.GenericExtend
