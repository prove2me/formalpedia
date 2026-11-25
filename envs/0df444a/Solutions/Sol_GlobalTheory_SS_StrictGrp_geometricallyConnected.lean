-- Prove2me | solution 1 for GlobalTheory.SS.StrictGrp.geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:49.343839+00:00
-- url     : https://prove2.me/submissions/5fdb2271-4019-4b27-a429-315281d7225c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGrpObjOfStrictBirationalLaw
import Theorems.Thm_GlobalTheory_SS_StrictGrp_isPullback_j
import Theorems.Thm_GlobalTheory_SS_StrictGrp_mem_range_generic
import Theorems.Thm_GlobalTheory_SS_StrictGrp_connectedSpace_of_factor
import Theorems.Thm_GlobalTheory_SS_CompatCrit_isPullback_j
import Theorems.Thm_GlobalTheory_SS_Model_isPullback_j
import Theorems.Thm_GlobalTheory_SS_Translates_isPullback_j
import Theorems.Thm_GlobalTheory_geometricallyIrreducible_of_isAlgClosed
import Theorems.Thm_GlobalTheory_isOpenImmersion_spMap_of_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_range_fst_residue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictGrp
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.StrictGrp
theorem _root_.solution (h : SH R K) (M : Model R A) (hM : M.Irr) [GeometricallyConnected A.hom] :
    GeometricallyConnected M.Y.hom := by
  obtain ⟨hD, -, hk, hF⟩ := h
  have := M.smooth
  refine ⟨fun L _ y Z a b hZ => ?_⟩
  by_cases hy : y (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R
  · let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    have hr : IsClosedImmersion r := .spec_of_surjective _ IsLocalRing.residue_surjective
    have : IrreducibleSpace ↥(pullback M.Y.hom r) := by
      have he := (pullback.fst M.Y.hom r).isClosedEmbedding.isEmbedding
      have h₁ : IsIrreducible (Set.range (pullback.fst M.Y.hom r)) := by
        rw [range_fst_residue]; exact hM
      have := Subtype.irreducibleSpace h₁
      exact he.toHomeomorph.irreducibleSpace_iff.2 this
    have h₂ := geometricallyIrreducible_of_isAlgClosed (pullback.snd M.Y.hom r)
    have : GeometricallyConnected (pullback.snd M.Y.hom r) := ⟨fun L _ y Z a b hZ => by
      have : IrreducibleSpace Z := h₂.geometrically_irreducibleSpace y a b hZ
      infer_instance⟩
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hl : IsLocalHom φ.hom := (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 hy
    have e : Spec.map φ = spMap (IsLocalRing.ResidueField.lift φ.hom) ≫ r := by
      rw [← Spec.map_comp]; congr 1
    rw [e] at hZ
    exact connectedSpace_of_factor (IsPullback.of_hasPullback _ _) _ hZ
  · have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
    have hr : Set.range y ⊆ Set.range (spMap (algebraMap R K)) := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q (IsLocalRing.closedPoint L)]
      exact mem_range_generic _ hy
    rw [← IsOpenImmersion.lift_fac _ _ hr] at hZ
    exact connectedSpace_of_factor (isPullback_j M) _ hZ
end GlobalTheory.SS.StrictGrp
