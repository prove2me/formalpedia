-- Prove2me | solution 1 for GlobalTheory.SS.StrictGrp.defAt_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:43.574798+00:00
-- url     : https://prove2.me/submissions/fe0a49b2-0428-4461-b810-66c186f7e72b

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
import Theorems.Thm_GlobalTheory_SS_StrictGrp_defAt_of_chart
import Theorems.Thm_GlobalTheory_SS_StrictGrp_isPullback_of_comm

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
namespace GlobalTheory.SS.StrictGrp
theorem _root_.solution {M : Model R A} {G : Model R A'} {N N' : Model R A''} {f : A ≅ A'} {g : M.Y ⟶ G.Y}
    [IsOpenImmersion g.left] (h : M.j ≫ g.left = f.hom.left ≫ G.j) {ψ : A ⟶ A''} {φ : A' ⟶ A''} {t : A'' ⟶ A''}
    {T : N.Y ⟶ N'.Y} (hT : N.j ≫ T.left = t.left ≫ N'.j) (e : ψ ≫ t = f.hom ≫ φ) {x : M.Y.left}
    (hx : DefAt M N ψ x) : DefAt G N' φ (g.left x) := by
  obtain ⟨U, k, hU, h₁, h₂⟩ := hx
  refine defAt_of_chart (U.ι ≫ g.left) (v := M.j ∣_ U) (u := (M.j ⁻¹ᵁ U).ι ≫ f.hom.left)
    ((isPullback_morphismRestrict M.j U).paste_vert (isPullback_of_comm h)) (k ≫ T.left) ?_ ?_ ⟨⟨x, hU⟩, rfl⟩
  · rw [Category.assoc, Over.w T, h₁, Category.assoc, Over.w g]
  · rw [← Category.assoc, h₂, Category.assoc, Category.assoc, hT, ← Category.assoc ψ.left, ← Over.comp_left, e]
    simp
end GlobalTheory.SS.StrictGrp
