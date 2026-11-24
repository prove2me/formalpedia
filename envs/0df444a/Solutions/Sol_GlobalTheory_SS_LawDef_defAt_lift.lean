-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.defAt_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:21.545089+00:00
-- url     : https://prove2.me/submissions/05812a86-6a0a-4ab5-930e-9a285cacee00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_ext
import Theorems.Thm_GlobalTheory_SS_LawDef_ext_test
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_mk
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_snd


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.LawDef
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A ⟶ A''}
    {y : M.Y.left} (h : DefAt M N f y) (h' : DefAt M P f' y) : DefAt M (N.prod P) (lift f f') y := by
  obtain ⟨U, g, hy, h⟩ := h
  obtain ⟨V, g', hy', h'⟩ := h'
  let i₁ := M.Y.left.homOfLE (inf_le_left : U ⊓ V ≤ U)
  let i₂ := M.Y.left.homOfLE (inf_le_right : U ⊓ V ≤ V)
  have e₁ : i₁ ≫ U.ι = (U ⊓ V).ι := Scheme.homOfLE_ι _ _
  have e₂ : i₂ ≫ V.ι = (U ⊓ V).ι := Scheme.homOfLE_ι _ _
  have w : (i₁ ≫ g) ≫ N.Y.hom = (i₂ ≫ g') ≫ P.Y.hom := by
    rw [Category.assoc, Category.assoc, h.1, h'.1, reassoc_of% e₁, reassoc_of% e₂]
  let G : (U ⊓ V).toScheme ⟶ (N.prod P).Y.left := pullback.lift _ _ w
  have G1 : G ≫ (fst N.Y P.Y).left = i₁ ≫ g := pullback.lift_fst _ _ _
  have G2 : G ≫ (snd N.Y P.Y).left = i₂ ≫ g' := pullback.lift_snd _ _ _
  refine defAt_mk M (N.prod P) _ (U ⊓ V).ι G ?_ ?_ ⟨y, hy, hy'⟩
  · have : (N.prod P).Y.hom = (fst N.Y P.Y).left ≫ N.Y.hom := (Over.w (fst N.Y P.Y)).symm
    rw [this, reassoc_of% G1, h.1, reassoc_of% e₁]
  · intro T t u e
    apply prod_ext
    · have := ext_test h t (u ≫ i₁) (by rw [Category.assoc, e₁, e])
      simp only [Category.assoc] at this ⊢
      rw [G1, this, prod_j_fst, ← Over.comp_left_assoc, lift_fst]
    · have := ext_test h' t (u ≫ i₂) (by rw [Category.assoc, e₂, e])
      simp only [Category.assoc] at this ⊢
      rw [G2, this, prod_j_snd, ← Over.comp_left_assoc, lift_snd]
end GlobalTheory.SS.LawDef
