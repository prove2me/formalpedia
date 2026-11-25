-- Prove2me | solution 1 for GlobalTheory.SS.Translates.exists_section_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:16.259361+00:00
-- url     : https://prove2.me/submissions/f231d3ae-82c4-4467-a1a7-6d1a3199861a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
import Theorems.Thm_GlobalTheory_SS_Translates_exists_section_fibre
import Theorems.Thm_GlobalTheory_range_fst_residue


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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.Translates
theorem _root_.solution [IsDomain R] [IsLocalRing R] (hR : SH R K) (M : Model R A) {z : M.Y.left}
    (hz : z ∈ M.sp) (hc : IsClosed {z}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) = z := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) := .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))) := by
    rw [range_fst_residue]; exact hz
  refine exists_section_fibre hR M y ?_
  have := hc.preimage (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _
    (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))).isClosedEmbedding.injective] at this
end GlobalTheory.SS.Translates
