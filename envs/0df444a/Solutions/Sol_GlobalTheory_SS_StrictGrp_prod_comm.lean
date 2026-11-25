-- Prove2me | solution 1 for GlobalTheory.SS.StrictGrp.prod_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:36.722869+00:00
-- url     : https://prove2.me/submissions/a4dc8d5c-c985-4ff3-9a65-40d987778d73

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
import Theorems.Thm_GlobalTheory_SS_StrictGrp_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_StrictGrp_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_FinUnion_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_FinUnion_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
theorem _root_.solution {B B' : Over (Sp K)} {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : M.Y ⟶ P.Y} {g' : N.Y ⟶ Q.Y} (h : M.j ≫ g.left = f.left ≫ P.j)
    (h' : N.j ≫ g'.left = f'.left ≫ Q.j) :
    (M.prod N).j ≫ (g ⊗ₘ g').left = (f ⊗ₘ f').left ≫ (P.prod Q).j := by
  apply Over.tensorObj_ext
  · change (_ ≫ _) ≫ (fst P.Y Q.Y).left = (_ ≫ _) ≫ (fst P.Y Q.Y).left
    rw [Category.assoc, Category.assoc, prod_j_fst, ← Over.comp_left, tensorHom_fst, Over.comp_left,
      ← Category.assoc, prod_j_fst, Category.assoc, h, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, tensorHom_fst]
  · change (_ ≫ _) ≫ (snd P.Y Q.Y).left = (_ ≫ _) ≫ (snd P.Y Q.Y).left
    rw [Category.assoc, Category.assoc, prod_j_snd, ← Over.comp_left, tensorHom_snd, Over.comp_left,
      ← Category.assoc, prod_j_snd, Category.assoc, h', ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, tensorHom_snd]
end GlobalTheory.SS.StrictGrp
