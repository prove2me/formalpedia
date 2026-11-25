-- Prove2me | solution 1 for GlobalTheory.SS.StrictGrp.defAt_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:44.274337+00:00
-- url     : https://prove2.me/submissions/0d3aa27a-03bd-4ed7-8b3b-558fa3a2ec01

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
import Theorems.Thm_GlobalTheory_SS_StrictGrp_defAt_of_chart
import Theorems.Thm_GlobalTheory_SS_StrictGrp_mem_range_generic
import Theorems.Thm_GlobalTheory_SS_CompatCrit_isPullback_j
import Theorems.Thm_GlobalTheory_SS_Model_isPullback_j
import Theorems.Thm_GlobalTheory_SS_Model_j_hom
import Theorems.Thm_GlobalTheory_SS_Translates_isPullback_j
import Theorems.Thm_GlobalTheory_isOpenImmersion_spMap_of_isDiscreteValuationRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsDomain R]
namespace GlobalTheory.SS.StrictGrp
theorem _root_.solution [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A) (N : Model R A') (f : A ⟶ A')
    {x : M.Y.left} (hx : x ∉ M.sp) : DefAt M N f x := by
  have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip this
  refine defAt_of_chart M.j (v := 𝟙 _) (u := 𝟙 _) (IsKernelPair.id_of_mono _) (f.left ≫ N.j) ?_ (by simp) ?_
  · rw [Category.assoc, N.j_hom, M.j_hom, ← Category.assoc, Over.w f]
  · obtain ⟨q, hq⟩ := mem_range_generic (K := K) (M.Y.hom x) hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) x q hq.symm
    exact ⟨z, hz⟩
end GlobalTheory.SS.StrictGrp
