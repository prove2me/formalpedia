-- Prove2me | solution 1 for GlobalTheory.T.modelGroupLaw_definedAt_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:36:01.752264+00:00
-- url     : https://prove2.me/submissions/59b9363a-8176-48ec-96f7-a643430e6739

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Theorems.Thm_GlobalTheory_SS_defAt_mul_twist


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  first | exact @GlobalTheory.SS.defAt_mul_twist | exact GlobalTheory.SS.defAt_mul_twist | (intros; apply GlobalTheory.SS.defAt_mul_twist <;> assumption)
end _root_.GlobalTheory.T
