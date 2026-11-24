-- Prove2me | solution 1 for GlobalTheory.SS.Translates.Ext.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:40.044179+00:00
-- url     : https://prove2.me/submissions/fb32e4ce-39a2-4b73-9b34-40fa457efc83

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
namespace Ext
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {X X' : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ N.Y.left} {i' : X' ⟶ N.Y.left} {g' : X' ⟶ P.Y.left}
    (h : Ext M N f i g) (h' : Ext N P f' i' g') :
    Ext M P (f ≫ f') (pullback.fst g i' ≫ i) (pullback.snd g i' ≫ g') := by
  refine ⟨by rw [Category.assoc, h'.1, ← pullback.condition_assoc, h.1, Category.assoc], fun T t a e => ?_⟩
  have h1 := h.2 T (t ≫ pullback.fst g i') a (by rw [Category.assoc, e])
  have h2 := h'.2 T (t ≫ pullback.snd g i') (a ≫ f.left)
    (by rw [Category.assoc, ← pullback.condition, ← Category.assoc, h1, Category.assoc])
  simpa using h2
end Ext
end GlobalTheory.SS.Translates
