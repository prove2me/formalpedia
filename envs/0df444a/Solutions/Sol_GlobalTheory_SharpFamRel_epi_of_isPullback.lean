-- Prove2me | solution 1 for GlobalTheory.SharpFamRel.epi_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:52:41.973516+00:00
-- url     : https://prove2.me/submissions/15fef716-b999-4fb2-83b8-dee3c311944f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel
namespace GlobalTheory.SharpFamRel
theorem _root_.solution {K : Type} [Field K] {S' : Scheme.{0}} {f : S' ⟶ Sp K} [Nonempty S'] {X₀ X : Scheme.{0}}
    {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀} (H : IsPullback h p p₀ f) : Epi h := by
  have hs : Surjective f := ⟨fun y => by
    obtain ⟨z⟩ := ‹Nonempty S'›
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have : Flat h := MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective h := MorphismProperty.of_isPullback H.flip hs
  exact Flat.epi_of_flat_of_surjective h
end GlobalTheory.SharpFamRel
