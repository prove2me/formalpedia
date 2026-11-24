-- Prove2me | solution 1 for GlobalTheory.SS.CompatCrit.isPullback_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:55.480297+00:00
-- url     : https://prove2.me/submissions/19df0a9d-2238-4b30-b636-7bbe094b7b6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.CompatCrit
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.CompatCrit
theorem _root_.solution (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w M.e.inv⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
end GlobalTheory.SS.CompatCrit
