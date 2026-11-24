-- Prove2me | solution 1 for GlobalTheory.SS.Translates.isoAt_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:20.785356+00:00
-- url     : https://prove2.me/submissions/97bf247f-ea6a-4e94-bff9-4f8e55235614

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
import Theorems.Thm_GlobalTheory_SS_Translates_isoAt_iff
import Theorems.Thm_GlobalTheory_SS_Translates_Ext_div

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
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R A''} {u : A ⟶ A'} {f' : A' ≅ A''}
    {X X' : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ P.Y.left} {i' : X' ⟶ N.Y.left} {g' : X' ⟶ P.Y.left}
    [IsOpenImmersion i] [IsOpenImmersion g] [IsOpenImmersion i'] [IsOpenImmersion g']
    (h : Ext M P (u ≫ f'.hom) i g) (h' : Ext N P f'.hom i' g') {o : X} {o' : X'} (e : g o = g' o') :
    IsoAt M N u (i o) := by
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback o o' e
  exact isoAt_iff.2 ⟨_, _, _, p, inferInstance, inferInstance, h.div h', by rw [Scheme.Hom.comp_apply, hp]⟩
end GlobalTheory.SS.Translates
