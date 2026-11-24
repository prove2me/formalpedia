-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.defAt_comp_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:54.177402+00:00
-- url     : https://prove2.me/submissions/e3b1cc79-ea5b-4703-a906-d9e9d46919c2

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
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_comp
import Theorems.Thm_GlobalTheory_SS_LawDef_sec_unique
import Theorems.Thm_GlobalTheory_SS_LawDef_sec_exists
import Theorems.Thm_GlobalTheory_SS_GI_defAt_comp


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
variable [IsLocalRing R]
namespace GlobalTheory.SS.LawDef
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {P : Model R A''}
    {f : A ⟶ A'} {f' : A' ⟶ A''} {p : 𝟙_ (Over (Sp K)) ⟶ A} {s : 𝟙_ (Over (Sp R)) ⟶ M.Y}
    {t : 𝟙_ (Over (Sp R)) ⟶ N.Y} (hs : Sec M p s) (ht : Sec N (p ≫ f) t) (h : DefAt M N f (sp0 s))
    (h' : DefAt N P f' (sp0 t)) : DefAt M P (f ≫ f') (sp0 s) := by
  obtain ⟨U, g, hy, h⟩ := h
  obtain ⟨t', ht', e⟩ := sec_exists h hs ⟨_, hy⟩ rfl
  rw [sec_unique ht ht', ← e] at h'
  exact defAt_comp h _ h'
end GlobalTheory.SS.LawDef
